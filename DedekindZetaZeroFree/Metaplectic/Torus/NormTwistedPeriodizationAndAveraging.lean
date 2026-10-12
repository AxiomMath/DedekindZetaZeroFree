module

public import DedekindZetaZeroFree.Metaplectic.Torus.PeriodizationAndAveraging

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := KPGlobalTorusFunctionData.G F ζ hζ
abbrev E := KPGlobalTorusFunctionData.E F ζ hζ

abbrev Polarization := KPGlobalTorusFunctionData.Polarization F ζ hζ

abbrev Smooth (P : Polarization F ζ hζ) :=
  KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P

local instance smoothTopology (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

theorem globalLevel_isCompact (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    IsCompact ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J) : Set (G F ζ hζ)) := by
  exact J.isCompact.image continuous_subtype_val

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] smoothTopology

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ModelData := KPGlobalTorusPeriodizationInverse.ModelData F ζ hζ

def normPower (s : ℂ) (t : E F ζ hζ) : ℂ :=
  Complex.exp (s * (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) : ℂ))

private theorem delta_pos (t : E F ζ hζ) :
    0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) := by
  exact_mod_cast pos_iff_ne_zero.mpr (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t))

private theorem normPower_one (s : ℂ) : normPower F ζ hζ s 1 = 1 := by
  simp [normPower]

private theorem normPower_mul (s : ℂ) (t u : E F ζ hζ) :
    normPower F ζ hζ s (t * u) = normPower F ζ hζ s t * normPower F ζ hζ s u := by
  simp only [normPower, map_mul, Units.val_mul, NNReal.coe_mul,
    Real.log_mul (ne_of_gt (delta_pos F ζ hζ t)) (ne_of_gt (delta_pos F ζ hζ u)),
    Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem normPower_cancel (s : ℂ) (t : E F ζ hζ) :
    normPower F ζ hζ s t * normPower F ζ hζ (-s) t = 1 := by
  simp only [normPower, neg_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private theorem normPower_continuous (s : ℂ) : Continuous (normPower F ζ hζ s) := by
  have hlog : ∀ t : E F ζ hζ,
      Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) =
        6 * Real.log (((KPGlobalCenterRationalCharacter.nu F ζ hζ t : ℝ≥0) : ℝ)) := by
    intro t
    rw [KPGlobalCenterRationalCharacter.nu_formula]
    change Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) =
      6 * Real.log ((((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) ^ (1 / 6 : ℝ))
    rw [Real.log_rpow (delta_pos F ζ hζ t)]
    ring
  have hc := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))
  have hl := hc.log (fun t => ne_of_gt (KPGlobalCenterRationalCharacter.nu_positive F ζ hζ t))
  change Continuous (fun t : E F ζ hζ => Complex.exp
    (s * (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) : ℂ)))
  simp only [hlog]
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_const.mul hl))).cexp

def normCharacter (s : ℂ) : E F ζ hζ →ₜ* ℂˣ where
  toFun t := Units.mk0 (normPower F ζ hζ s t) (Complex.exp_ne_zero _)
  map_one' := by
    apply Units.ext
    exact normPower_one F ζ hζ s
  map_mul' t u := by
    apply Units.ext
    exact normPower_mul F ζ hζ s t u
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    constructor
    · exact normPower_continuous F ζ hζ s
    · change Continuous (fun t => (normPower F ζ hζ s t)⁻¹)
      have hi : ∀ t, (normPower F ζ hζ s t)⁻¹ = normPower F ζ hζ (-s) t := by
        intro t
        exact inv_eq_of_mul_eq_one_right (normPower_cancel F ζ hζ s t)
      simp only [hi]
      exact normPower_continuous F ζ hζ (-s)

 theorem normPower_entire (t : E F ζ hζ) :
    Differentiable ℂ (fun s => normPower F ζ hζ s t) := by
  exact (differentiable_id.mul_const _).cexp

 theorem delta_rational (y : Fˣ) :
    KPGlobalTorusFunctionData.delta F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ y) = 1 := by
  apply Units.ext
  apply NNReal.rpow_left_injective (x := (1 / 6 : ℝ)) (by norm_num)
  have h := KPGlobalTorusPeriodizationInverse.rational_representative_norm F ζ hζ y
  have he := congrArg Units.val h
  simpa [KPGlobalCenterRationalCharacter.nu, KPGlobalCenterRationalCharacter.sixthPower,
    KPGlobalTorusPeriodizationInverse.rationalLift] using he

 theorem normCharacter_rational (s : ℂ) (y : Fˣ) :
    normCharacter F ζ hζ s (KPGlobalTorusFunctionData.s F ζ hζ y) = 1 := by
  apply Units.ext
  change normPower F ζ hζ s (KPGlobalTorusFunctionData.s F ζ hζ y) = 1
  simp [normPower, delta_rational]

def twist (P : Polarization F ζ hζ) (s : ℂ) : Polarization F ζ hζ where
  H := P.H
  closed := P.closed
  abelian := P.abelian
  contains_center := P.contains_center
  character := P.character * (normCharacter F ζ hζ s).comp
    ⟨P.H.subtype, continuous_subtype_val⟩

def scalarNormTwist (P : Polarization F ζ hζ) (s : ℂ) :
    KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (twist F ζ hζ P s) where
  toFun f := ⟨fun t => normPower F ζ hζ s t * f.val t, by
    intro h t
    dsimp only
    rw [normPower_mul, f.property h t]
    change normPower F ζ hζ s h.val * normPower F ζ hζ s t *
      ((P.character h : ℂ) * f.val t) =
      ((P.character h : ℂ) * normPower F ζ hζ s h.val) * _
    ring⟩
  map_add' f g := by ext t; simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c f := by ext t; simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def scalarNormUntwist (P : Polarization F ζ hζ) (s : ℂ) :
    KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (twist F ζ hζ P s) →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P where
  toFun f := ⟨fun t => normPower F ζ hζ (-s) t * f.val t, by
    intro h t
    dsimp only
    rw [normPower_mul, f.property h t]
    change _ = (P.character h : ℂ) * _
    have hc := normPower_cancel F ζ hζ s h.val
    change normPower F ζ hζ (-s) h.val * normPower F ζ hζ (-s) t *
      (((P.character h : ℂ) * normPower F ζ hζ s h.val) * f.val t) = _
    calc
      _ = (normPower F ζ hζ s h.val * normPower F ζ hζ (-s) h.val) *
          ((P.character h : ℂ) * (normPower F ζ hζ (-s) t * f.val t)) := by ring
      _ = _ := by rw [hc, one_mul]⟩
  map_add' f g := by ext t; simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c f := by ext t; simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def scalarNormTwistEquiv (P : Polarization F ζ hζ) (s : ℂ) :
    KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P ≃ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (twist F ζ hζ P s) :=
  LinearEquiv.ofLinear (scalarNormTwist F ζ hζ P s) (scalarNormUntwist F ζ hζ P s)
    (by ext f t; change normPower F ζ hζ s t * (normPower F ζ hζ (-s) t * f.val t) = f.val t
        rw [← mul_assoc, normPower_cancel, one_mul])
    (by ext f t; change normPower F ζ hζ (-s) t * (normPower F ζ hζ s t * f.val t) = f.val t
        rw [← mul_assoc, mul_comm (normPower F ζ hζ (-s) t), normPower_cancel, one_mul])

theorem delta_compact_subgroup (H : Subgroup (E F ζ hζ))
    (hc : IsCompact (H : Set (E F ζ hζ))) (t : H) :
    KPGlobalTorusFunctionData.delta F ζ hζ t.val = 1 := by
  let f : E F ζ hζ → ℝ := fun a =>
    (((KPGlobalCenterRationalCharacter.nu F ζ hζ a : ℝ≥0) : ℝ))
  have hp (a : E F ζ hζ) : 0 < f a := KPGlobalCenterRationalCharacter.nu_positive F ζ hζ a
  have hf : Continuous f := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))
  obtain ⟨k, hk, hmax⟩ := hc.exists_isMaxOn ⟨1, H.one_mem⟩ hf.continuousOn
  have hmul (a b : E F ζ hζ) : f (a * b) = f a * f b := by
    simp [f, map_mul, Units.val_mul, NNReal.coe_mul]
  have ht : f t.val ≤ 1 := by
    have h : f (k * t.val) ≤ f k := hmax (H.mul_mem hk t.property)
    rw [hmul] at h
    nlinarith [hp k]
  have hi : 1 ≤ f t.val := by
    have h : f (k * t.val⁻¹) ≤ f k := hmax (H.mul_mem hk (H.inv_mem t.property))
    rw [hmul] at h
    have hprod : f t.val * f t.val⁻¹ = 1 := by rw [← hmul]; simp [f]
    nlinarith [hp k, hp t.val, hp t.val⁻¹]
  have he : KPGlobalCenterRationalCharacter.nu F ζ hζ t.val = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    exact le_antisymm ht hi
  apply Units.ext
  apply NNReal.rpow_left_injective (x := (1 / 6 : ℝ)) (by norm_num)
  have he' := congrArg Units.val he
  simpa [KPGlobalCenterRationalCharacter.nu, KPGlobalCenterRationalCharacter.sixthPower] using he'

theorem normPower_compact_subgroup (H : Subgroup (E F ζ hζ))
    (hc : IsCompact (H : Set (E F ζ hζ))) (s : ℂ) (t : H) :
    normPower F ζ hζ s t.val = 1 := by
  simp [normPower, delta_compact_subgroup F ζ hζ H hc t]

def NormPowerArchSmooth (s : ℂ) : Prop :=
  ∀ t : E F ζ hζ, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun z => normPower F ζ hζ s (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * t))
      (KPGlobalTorusFunctionData.torusArchDomain F)

def NormPowerLevelTrivial (s : ℂ) : Prop :=
  ∀ (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (j : E F ζ hζ), j ∈ ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) → normPower F ζ hζ s j = 1

theorem normPowerArchSmooth_of_delta_smooth
    (hd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (((KPGlobalTorusFunctionData.delta F ζ hζ
        (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z) : ℝ≥0) : ℝ)))
      (KPGlobalTorusFunctionData.torusArchDomain F)) (s : ℂ) :
    NormPowerArchSmooth F ζ hζ s := by
  intro t
  have hdt : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (((KPGlobalTorusFunctionData.delta F ζ hζ
        (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * t) : ℝ≥0) : ℝ)))
      (KPGlobalTorusFunctionData.torusArchDomain F) := by
    simpa only [map_mul, Units.val_mul, NNReal.coe_mul] using hd.mul contDiffOn_const
  have hl := hdt.log (fun z _ => ne_of_gt (delta_pos F ζ hζ _))
  exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hl)).cexp

theorem normPowerArchSmooth_of_chart_formula
    (hδ : ∀ z ∈ KPGlobalTorusFunctionData.torusArchDomain F,
      (((KPGlobalTorusFunctionData.delta F ζ hζ
        (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z) : ℝ≥0) : ℝ)) =
          ∏ w : InfinitePlace F, ‖z w‖ ^ 2) (s : ℂ) :
    NormPowerArchSmooth F ζ hζ s := by
  apply normPowerArchSmooth_of_delta_smooth F ζ hζ _ s
  have hp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : KPGlobalTorusFunctionData.TorusArch F => ∏ w : InfinitePlace F, ‖z w‖ ^ 2) := by
    exact contDiff_prod (fun w _ => (contDiff_apply ℝ ℂ w).norm_sq ℝ)
  exact hp.contDiffOn.congr (fun z hz => hδ z hz)

theorem normPowerArchSmooth_neg (s : ℂ) (ha : NormPowerArchSmooth F ζ hζ s) :
    NormPowerArchSmooth F ζ hζ (-s) := by
  intro t
  have hi (z : KPGlobalTorusFunctionData.TorusArch F) :
      normPower F ζ hζ (-s) (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * t) =
        (normPower F ζ hζ s (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * t))⁻¹ :=
    (inv_eq_of_mul_eq_one_right (normPower_cancel F ζ hζ s _)).symm
  simp only [hi]
  exact (ha t).inv (fun z _ => Complex.exp_ne_zero _)

theorem normPowerLevelTrivial_neg (s : ℂ) (hl : NormPowerLevelTrivial F ζ hζ s) :
    NormPowerLevelTrivial F ζ hζ (-s) := by
  intro J j hj
  have hc := normPower_cancel F ζ hζ s j
  simpa only [hl J j hj, one_mul] using hc

theorem normPowerLevelTrivial_of_torus_closed
    (ht : IsClosed ((KPGlobalTorusFunctionData.torus F ζ hζ) : Set (G F ζ hζ)))
    (s : ℂ) : NormPowerLevelTrivial F ζ hζ s := by
  intro J j hj
  let H := (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
    (KPGlobalTorusFunctionData.torus F ζ hζ).subtype
  have hc : IsCompact (H : Set (E F ζ hζ)) :=
    ht.isClosedEmbedding_subtypeVal.isCompact_preimage (globalLevel_isCompact F ζ hζ J)
  exact normPower_compact_subgroup F ζ hζ H hc s ⟨j, hj⟩

theorem scalarNormTwist_mem_smoothLevel (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P)
    (hf : f ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P J) :
    scalarNormTwist F ζ hζ P s f ∈
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ (twist F ζ hζ P s) J := by
  constructor
  · intro t
    exact (ha t).mul (hf.1 t)
  · intro j
    apply Subtype.ext
    funext t
    change normPower F ζ hζ s (t * j.val) * f.val (t * j.val) =
      normPower F ζ hζ s t * f.val t
    rw [normPower_mul, hl J j.val j.property, mul_one]
    rw [KPGlobalTorusFunctionData.rightLevel_covariance _ _ _ ⟨f, hf.2⟩ t j.val j.property]

theorem scalarNormTwist_mem_smoothUnion (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P)
    (hf : f ∈ Smooth F ζ hζ P) :
    scalarNormTwist F ζ hζ P s f ∈ Smooth F ζ hζ (twist F ζ hζ P s) := by
  refine Submodule.iSup_induction (p := fun J => KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P J)
    (motive := fun f => scalarNormTwist F ζ hζ P s f ∈ Smooth F ζ hζ (twist F ζ hζ P s)) hf ?_ ?_ ?_
  · intro J f hf
    exact (le_iSup (fun J => KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (twist F ζ hζ P s) J) J) (scalarNormTwist_mem_smoothLevel F ζ hζ P s ha hl J f hf)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro f g hf hg
    rw [map_add]; exact Submodule.add_mem _ hf hg

  theorem scalarNormUntwist_mem_smoothLevel (P : Polarization F ζ hζ) (s : ℂ)
      (ha : NormPowerArchSmooth F ζ hζ (-s)) (hl : NormPowerLevelTrivial F ζ hζ (-s))
      (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
      (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (twist F ζ hζ P s))
      (hf : f ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ (twist F ζ hζ P s) J) :
      scalarNormUntwist F ζ hζ P s f ∈
        KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P J := by
    constructor
    · intro t
      exact (ha t).mul (hf.1 t)
    · intro j
      apply Subtype.ext
      funext t
      change normPower F ζ hζ (-s) (t * j.val) * f.val (t * j.val) =
        normPower F ζ hζ (-s) t * f.val t
      rw [normPower_mul, hl J j.val j.property, mul_one]
      rw [KPGlobalTorusFunctionData.rightLevel_covariance _ _ _ ⟨f, hf.2⟩ t j.val j.property]

  theorem scalarNormUntwist_mem_smoothUnion (P : Polarization F ζ hζ) (s : ℂ)
      (ha : NormPowerArchSmooth F ζ hζ (-s)) (hl : NormPowerLevelTrivial F ζ hζ (-s))
      (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (twist F ζ hζ P s))
      (hf : f ∈ Smooth F ζ hζ (twist F ζ hζ P s)) :
      scalarNormUntwist F ζ hζ P s f ∈ Smooth F ζ hζ P := by
    refine Submodule.iSup_induction
      (p := fun J => KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ (twist F ζ hζ P s) J)
      (motive := fun f => scalarNormUntwist F ζ hζ P s f ∈ Smooth F ζ hζ P) hf ?_ ?_ ?_
    · intro J f hf
      exact (le_iSup (fun J => KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P J) J)
        (scalarNormUntwist_mem_smoothLevel F ζ hζ P s ha hl J f hf)
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro f g hf hg
      rw [map_add]; exact Submodule.add_mem _ hf hg

  def smoothNormTwistLinearEquiv (P : Polarization F ζ hζ) (s : ℂ)
      (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
      (hai : NormPowerArchSmooth F ζ hζ (-s)) (hli : NormPowerLevelTrivial F ζ hζ (-s)) :
      Smooth F ζ hζ P ≃ₗ[ℂ] Smooth F ζ hζ (twist F ζ hζ P s) where
    toFun f := ⟨scalarNormTwist F ζ hζ P s f.val,
      scalarNormTwist_mem_smoothUnion F ζ hζ P s ha hl f.val f.property⟩
    invFun f := ⟨scalarNormUntwist F ζ hζ P s f.val,
      scalarNormUntwist_mem_smoothUnion F ζ hζ P s hai hli f.val f.property⟩
    left_inv f := by
      apply Subtype.ext
      exact (scalarNormTwistEquiv F ζ hζ P s).left_inv f.val
    right_inv f := by
      apply Subtype.ext
      exact (scalarNormTwistEquiv F ζ hζ P s).right_inv f.val
    map_add' f g := by
      apply Subtype.ext
      exact (scalarNormTwist F ζ hζ P s).map_add f.val g.val
    map_smul' c f := by
      apply Subtype.ext
      exact (scalarNormTwist F ζ hζ P s).map_smul c f.val

theorem smoothUnion_linearMap_continuous_of_stages (P Q : Polarization F ζ hζ)
    (A : Smooth F ζ hζ P →ₗ[ℂ] Smooth F ζ hζ Q)
    (hA : ∀ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      @Continuous (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P J)
        (Smooth F ζ hζ Q)
        (KPGlobalTorusFunctionData.smoothLevelTopology P.H P.character.toMonoidHom
          (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
          (KPGlobalTorusFunctionData.torusArchDomain F) (KPGlobalTorusFunctionData.torusArchDomain_open F)
          ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
            (KPGlobalTorusFunctionData.torus F ζ hζ).subtype))
        (KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ Q)
        (A ∘ KPGlobalTorusFunctionData.stageInclusion P.H P.character.toMonoidHom
          (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
          (fun J => (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
            (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) J)) : Continuous A := by
  let p := fun q : KPGlobalTorusFunctionData.finalSeminorms P.H P.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    (fun J => (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) => q.val
  let q := fun q : KPGlobalTorusFunctionData.finalSeminorms Q.H Q.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    (fun J => (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) => q.val
  have hp : WithSeminorms p := ⟨rfl⟩
  have hq : WithSeminorms q := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  apply WithSeminorms.continuous_of_continuous_comp
    (E := Smooth F ζ hζ P) (F := Smooth F ζ hζ Q)
    (𝕝 := ℂ) (𝕝₂ := ℂ) (τ₁₂ := RingHom.id ℂ) hq A
  intro r
  let u : KPGlobalTorusFunctionData.finalSeminorms P.H P.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    (fun J => (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) :=
    ⟨r.val.comp A, fun J => by
      letI := KPGlobalTorusFunctionData.smoothLevelTopology P.H P.character.toMonoidHom
        (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
        (KPGlobalTorusFunctionData.torusArchDomain F) (KPGlobalTorusFunctionData.torusArchDomain_open F)
        ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
      exact (hq.continuous_seminorm r).comp (hA J)⟩
  exact hp.continuous_seminorm u

def stageNormTwist (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P J →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ (twist F ζ hζ P s) J :=
  (scalarNormTwist F ζ hζ P s).restrict
    (scalarNormTwist_mem_smoothLevel F ζ hζ P s ha hl J)

def stageNormUntwist (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ (-s)) (hl : NormPowerLevelTrivial F ζ hζ (-s))
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ (twist F ζ hζ P s) J →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P J :=
  (scalarNormUntwist F ζ hζ P s).restrict
    (scalarNormUntwist_mem_smoothLevel F ζ hζ P s ha hl J)

theorem stageNormTwist_continuous (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    letI := KPGlobalTorusFunctionData.smoothLevelTopology P.H P.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
    letI := KPGlobalTorusFunctionData.smoothLevelTopology (twist F ζ hζ P s).H
      (twist F ζ hζ P s).character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
    Continuous (stageNormTwist F ζ hζ P s ha hl J) := by
  apply JetMultiplierRaw.linearMap_continuous
    P.H P.character.toMonoidHom (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
    (KPGlobalTorusFunctionData.torusArchDomain F) (KPGlobalTorusFunctionData.torusArchDomain_open F)
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
    (twist F ζ hζ P s).character.toMonoidHom (stageNormTwist F ζ hζ P s ha hl J)
    (normPower F ζ hζ s) ha
  intro f t
  rfl

theorem stageNormUntwist_continuous (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ (-s)) (hl : NormPowerLevelTrivial F ζ hζ (-s))
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    letI := KPGlobalTorusFunctionData.smoothLevelTopology (twist F ζ hζ P s).H
      (twist F ζ hζ P s).character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
    letI := KPGlobalTorusFunctionData.smoothLevelTopology P.H P.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
    Continuous (stageNormUntwist F ζ hζ P s ha hl J) := by
  apply JetMultiplierRaw.linearMap_continuous
    P.H (twist F ζ hζ P s).character.toMonoidHom (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
    (KPGlobalTorusFunctionData.torusArchDomain F) (KPGlobalTorusFunctionData.torusArchDomain_open F)
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
    P.character.toMonoidHom (stageNormUntwist F ζ hζ P s ha hl J)
    (normPower F ζ hζ (-s)) ha
  intro f t
  rfl

theorem smoothNormTwistLinearEquiv_continuous (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (hai : NormPowerArchSmooth F ζ hζ (-s)) (hli : NormPowerLevelTrivial F ζ hζ (-s)) :
    Continuous (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli) := by
  apply smoothUnion_linearMap_continuous_of_stages F ζ hζ P (twist F ζ hζ P s)
    (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli).toLinearMap
  intro J
  letI := KPGlobalTorusFunctionData.smoothLevelTopology P.H P.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
  letI := KPGlobalTorusFunctionData.smoothLevelTopology (twist F ζ hζ P s).H
    (twist F ζ hζ P s).character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
  have hc := KPGlobalTorusFunctionData.stageInclusion_continuous
    (twist F ζ hζ P s).H (twist F ζ hζ P s).character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    (fun J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
      (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) J
  exact hc.comp (stageNormTwist_continuous F ζ hζ P s ha hl J)

theorem smoothNormTwistLinearEquiv_symm_continuous (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (hai : NormPowerArchSmooth F ζ hζ (-s)) (hli : NormPowerLevelTrivial F ζ hζ (-s)) :
    Continuous (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli).symm := by
  apply smoothUnion_linearMap_continuous_of_stages F ζ hζ (twist F ζ hζ P s) P
    (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli).symm.toLinearMap
  intro J
  letI := KPGlobalTorusFunctionData.smoothLevelTopology P.H P.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
  letI := KPGlobalTorusFunctionData.smoothLevelTopology (twist F ζ hζ P s).H
    (twist F ζ hζ P s).character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
  have hc := KPGlobalTorusFunctionData.stageInclusion_continuous
    P.H P.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ) (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    (fun J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
      (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) J
  exact hc.comp (stageNormUntwist_continuous F ζ hζ P s hai hli J)

def smoothNormTwistContinuousLinearEquiv (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (hai : NormPowerArchSmooth F ζ hζ (-s)) (hli : NormPowerLevelTrivial F ζ hζ (-s))
    (hc : Continuous (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli))
    (hci : Continuous (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli).symm) :
    Smooth F ζ hζ P ≃L[ℂ] Smooth F ζ hζ (twist F ζ hζ P s) :=
  { smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli with
    continuous_toFun := hc
    continuous_invFun := hci }

@[simp] theorem smoothNormTwistContinuousLinearEquiv_formula
    (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (hai : NormPowerArchSmooth F ζ hζ (-s)) (hli : NormPowerLevelTrivial F ζ hζ (-s))
    (hc : Continuous (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli))
    (hci : Continuous (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli).symm)
    (f : Smooth F ζ hζ P) (t : E F ζ hζ) :
    (smoothNormTwistContinuousLinearEquiv F ζ hζ P s ha hl hai hli hc hci f).val.val t =
      normPower F ζ hζ s t * f.val.val t := rfl

@[simp] theorem smoothNormTwistContinuousLinearEquiv_inverse_formula
    (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (hai : NormPowerArchSmooth F ζ hζ (-s)) (hli : NormPowerLevelTrivial F ζ hζ (-s))
    (hc : Continuous (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli))
    (hci : Continuous (smoothNormTwistLinearEquiv F ζ hζ P s ha hl hai hli).symm)
    (f : Smooth F ζ hζ (twist F ζ hζ P s)) (t : E F ζ hζ) :
    ((smoothNormTwistContinuousLinearEquiv F ζ hζ P s ha hl hai hli hc hci).symm f).val.val t =
      normPower F ζ hζ (-s) t * f.val.val t := rfl

def normTwistOfConditions (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s) :
    Smooth F ζ hζ P ≃L[ℂ] Smooth F ζ hζ (twist F ζ hζ P s) :=
  smoothNormTwistContinuousLinearEquiv F ζ hζ P s ha hl
    (normPowerArchSmooth_neg F ζ hζ s ha) (normPowerLevelTrivial_neg F ζ hζ s hl)
    (smoothNormTwistLinearEquiv_continuous F ζ hζ P s ha hl _ _)
    (smoothNormTwistLinearEquiv_symm_continuous F ζ hζ P s ha hl _ _)

@[simp] theorem normTwistOfConditions_formula (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (f : Smooth F ζ hζ P) (t : E F ζ hζ) :
    (normTwistOfConditions F ζ hζ P s ha hl f).val.val t =
      normPower F ζ hζ s t * f.val.val t := rfl

@[simp] theorem normTwistOfConditions_inverse_formula (P : Polarization F ζ hζ) (s : ℂ)
    (ha : NormPowerArchSmooth F ζ hζ s) (hl : NormPowerLevelTrivial F ζ hζ s)
    (f : Smooth F ζ hζ (twist F ζ hζ P s)) (t : E F ζ hζ) :
    ((normTwistOfConditions F ζ hζ P s ha hl).symm f).val.val t =
      normPower F ζ hζ (-s) t * f.val.val t := rfl

def normTwist (P : Polarization F ζ hζ) (s : ℂ) :
    Smooth F ζ hζ P ≃L[ℂ] Smooth F ζ hζ (twist F ζ hζ P s) :=
  normTwistOfConditions F ζ hζ P s
    (normPowerArchSmooth_of_chart_formula F ζ hζ
      (AnalyticInputs.delta_chart_formula F ζ hζ) s)
    (normPowerLevelTrivial_of_torus_closed F ζ hζ
      (AnalyticInputs.actualtorusclosed F ζ hζ) s)

 theorem normTwist_formula (P : Polarization F ζ hζ) (s : ℂ)
    (f : Smooth F ζ hζ P) (t : E F ζ hζ) :
    (normTwist F ζ hζ P s f).val.val t = normPower F ζ hζ s t * f.val.val t := rfl

 theorem normTwist_inverse_formula (P : Polarization F ζ hζ) (s : ℂ)
    (f : Smooth F ζ hζ (twist F ζ hζ P s)) (t : E F ζ hζ) :
    ((normTwist F ζ hζ P s).symm f).val.val t =
      normPower F ζ hζ (-s) t * f.val.val t := by
  have h := normTwist_formula F ζ hζ P s ((normTwist F ζ hζ P s).symm f) t
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [h, ← mul_assoc, mul_comm (normPower F ζ hζ (-s) t), normPower_cancel, one_mul]

abbrev rationalModel := KPGlobalTorusPeriodizationInverse.rationalModel F ζ hζ
abbrev productModel (C : ModelData F ζ hζ) :=
  KPGlobalTorusPeriodizationInverse.productModel F ζ hζ C
abbrev Rational (s : ℂ) := Smooth F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)
abbrev Product (C : ModelData F ζ hζ) (s : ℂ) :=
  Smooth F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)

def twistedP (C : ModelData F ζ hζ) (s : ℂ) :
    Product F ζ hζ C s →L[ℂ] Rational F ζ hζ s :=
  (normTwist F ζ hζ (rationalModel F ζ hζ) s).toContinuousLinearMap.comp
    ((KPGlobalTorusPeriodizationInverse.periodization F ζ hζ C).comp
      (normTwist F ζ hζ (productModel F ζ hζ C) s).symm.toContinuousLinearMap)

def twistedQ (C : ModelData F ζ hζ) (s : ℂ) :
    Rational F ζ hζ s →L[ℂ] Product F ζ hζ C s :=
  (normTwist F ζ hζ (productModel F ζ hζ C) s).toContinuousLinearMap.comp
    ((KPGlobalTorusPeriodizationInverse.averaging F ζ hζ C).comp
      (normTwist F ζ hζ (rationalModel F ζ hζ) s).symm.toContinuousLinearMap)

 theorem twistedP_twistedQ (C : ModelData F ζ hζ) (s : ℂ) (f : Rational F ζ hζ s) :
    twistedP F ζ hζ C s (twistedQ F ζ hζ C s f) = f := by
  simp only [twistedP, twistedQ, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    KPGlobalTorusPeriodizationInverse.periodization_averaging,
    KPGlobalTorusPeriodizationInverse.averaging_periodization,
    ContinuousLinearEquiv.apply_symm_apply]

 theorem twistedQ_twistedP (C : ModelData F ζ hζ) (s : ℂ) (f : Product F ζ hζ C s) :
    twistedQ F ζ hζ C s (twistedP F ζ hζ C s f) = f := by
  simp only [twistedP, twistedQ, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    KPGlobalTorusPeriodizationInverse.periodization_averaging,
    KPGlobalTorusPeriodizationInverse.averaging_periodization,
    ContinuousLinearEquiv.apply_symm_apply]

 theorem twistedP_transport (C : ModelData F ζ hζ) (s : ℂ)
    (f : Smooth F ζ hζ (productModel F ζ hζ C)) :
    twistedP F ζ hζ C s (normTwist F ζ hζ (productModel F ζ hζ C) s f) =
      normTwist F ζ hζ (rationalModel F ζ hζ) s
        (KPGlobalTorusPeriodizationInverse.periodization F ζ hζ C f) := by
  simp [twistedP]

 theorem twistedQ_transport (C : ModelData F ζ hζ) (s : ℂ)
    (f : Smooth F ζ hζ (rationalModel F ζ hζ)) :
    twistedQ F ζ hζ C s (normTwist F ζ hζ (rationalModel F ζ hζ) s f) =
      normTwist F ζ hζ (productModel F ζ hζ C) s
        (KPGlobalTorusPeriodizationInverse.averaging F ζ hζ C f) := by
  simp [twistedQ]

private theorem normTwist_rightAction (P : Polarization F ζ hζ) (s : ℂ)
    (a : E F ζ hζ) (f : Smooth F ζ hζ P) :
    KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ (twist F ζ hζ P s) a
      (normTwist F ζ hζ P s f) = normPower F ζ hζ s a •
        normTwist F ζ hζ P s (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P a f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change (normTwist F ζ hζ P s f).val.val (t * a) =
    normPower F ζ hζ s a * (normTwist F ζ hζ P s
      (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P a f)).val.val t
  rw [normTwist_formula, normTwist_formula,
    KPGlobalTorusPeriodizationInverse.rightAction_formula, normPower_mul]
  ring

 theorem twistedP_intertwines (C : ModelData F ζ hζ) (s : ℂ)
    (a : E F ζ hζ) (f : Product F ζ hζ C s) :
    twistedP F ζ hζ C s
        (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
          (twist F ζ hζ (productModel F ζ hζ C) s) a f) =
      KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
        (twist F ζ hζ (rationalModel F ζ hζ) s) a (twistedP F ζ hζ C s f) := by
  obtain ⟨u, rfl⟩ := (normTwist F ζ hζ (productModel F ζ hζ C) s).surjective f
  rw [normTwist_rightAction, map_smul, twistedP_transport, twistedP_transport,
    normTwist_rightAction, KPGlobalTorusPeriodizationInverse.periodization_intertwines]

 theorem twistedQ_intertwines (C : ModelData F ζ hζ) (s : ℂ)
    (a : E F ζ hζ) (f : Rational F ζ hζ s) :
    twistedQ F ζ hζ C s
        (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
          (twist F ζ hζ (rationalModel F ζ hζ) s) a f) =
      KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
        (twist F ζ hζ (productModel F ζ hζ C) s) a (twistedQ F ζ hζ C s f) := by
  obtain ⟨u, rfl⟩ := (normTwist F ζ hζ (rationalModel F ζ hζ) s).surjective f
  rw [normTwist_rightAction, map_smul, twistedQ_transport, twistedQ_transport,
    normTwist_rightAction, KPGlobalTorusPeriodizationInverse.averaging_intertwines]

 theorem twistedP_rational_formula (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.PeriodizationRepresentatives F ζ hζ C)
    (hr : ∀ a, ∃ y : Fˣ, r.lift a = KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y)
    (f : Product F ζ hζ C s) (t : E F ζ hζ) :
    (twistedP F ζ hζ C s f).val.val t = ∑' a, f.val.val ((r.lift a).val * t) := by
  change (normTwist F ζ hζ (rationalModel F ζ hζ) s
    (KPGlobalTorusPeriodizationInverse.periodization F ζ hζ C
      ((normTwist F ζ hζ (productModel F ζ hζ C) s).symm f))).val.val t = _
  rw [normTwist_formula, KPGlobalTorusPeriodizationInverse.periodization_rational_formula
    F ζ hζ C r hr, ← tsum_mul_left]
  apply tsum_congr
  intro a
  rw [normTwist_inverse_formula, normPower_mul]
  obtain ⟨y, hy⟩ := hr a
  have hn : normPower F ζ hζ (-s) (r.lift a).val = 1 := by
    rw [hy]
    change normPower F ζ hζ (-s) (KPGlobalTorusFunctionData.s F ζ hζ y) = 1
    simp [normPower, delta_rational]
  rw [hn, one_mul, ← mul_assoc, normPower_cancel, one_mul]

def twistedIntegrand (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ)
    (x : KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C) : ℂ :=
  (((twist F ζ hζ (productModel F ζ hζ C) s).character (r.lift x))⁻¹ : ℂˣ) *
    f.val.val ((r.lift x).val * t)

private theorem twistedIntegrand_eq (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ) :
    twistedIntegrand F ζ hζ C s r f t = fun x =>
      normPower F ζ hζ s t * KPGlobalTorusPeriodizationInverse.averagingIntegrand F ζ hζ C r
        ((normTwist F ζ hζ (rationalModel F ζ hζ) s).symm f) t x := by
  funext x
  simp only [twistedIntegrand, KPGlobalTorusPeriodizationInverse.averagingIntegrand,
    normTwist_inverse_formula, normPower_mul]
  simp only [twist, ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    Units.val_inv_eq_inv_val, Units.val_mul]
  change (((productModel F ζ hζ C).character (r.lift x) : ℂ) *
    normPower F ζ hζ s (r.lift x).val)⁻¹ * f.val.val ((r.lift x).val * t) = _
  have hi : (normPower F ζ hζ s (r.lift x).val)⁻¹ =
      normPower F ζ hζ (-s) (r.lift x).val :=
    inv_eq_of_mul_eq_one_right (normPower_cancel F ζ hζ s (r.lift x).val)
  rw [mul_inv, hi]
  have hc := normPower_cancel F ζ hζ s t
  change _ = normPower F ζ hζ s t *
    ((((productModel F ζ hζ C).character (r.lift x) : ℂ)⁻¹) *
      (normPower F ζ hζ (-s) (r.lift x).val * normPower F ζ hζ (-s) t *
        f.val.val ((r.lift x).val * t)))
  linear_combination -(((productModel F ζ hζ C).character (r.lift x) : ℂ)⁻¹ *
    normPower F ζ hζ (-s) (r.lift x).val * f.val.val ((r.lift x).val * t)) * hc

 theorem twistedIntegrand_independent (C : ModelData F ζ hζ) (s : ℂ)
    (r r' : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ) :
    twistedIntegrand F ζ hζ C s r f t = twistedIntegrand F ζ hζ C s r' f t := by
  rw [twistedIntegrand_eq, twistedIntegrand_eq]
  funext x
  rw [KPGlobalTorusPeriodizationInverse.averagingIntegrand_independent F ζ hζ C r r']

 theorem twistedIntegrand_integrable (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ) :
    Integrable (twistedIntegrand F ζ hζ C s r f t)
      (KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C) := by
  rw [twistedIntegrand_eq]
  exact (KPGlobalTorusPeriodizationInverse.averagingIntegrand_integrable F ζ hζ C r
    ((normTwist F ζ hζ (rationalModel F ζ hζ) s).symm f) t).const_mul _

 theorem twistedQ_formula (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ) :
    (twistedQ F ζ hζ C s f).val.val t =
      ∫ x, twistedIntegrand F ζ hζ C s r f t
        x ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C := by
  change (normTwist F ζ hζ (productModel F ζ hζ C) s
    (KPGlobalTorusPeriodizationInverse.averaging F ζ hζ C
      ((normTwist F ζ hζ (rationalModel F ζ hζ) s).symm f))).val.val t = _
  rw [normTwist_formula, KPGlobalTorusPeriodizationInverse.averaging_formula F ζ hζ C r,
    twistedIntegrand_eq, integral_const_mul]

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport

end
