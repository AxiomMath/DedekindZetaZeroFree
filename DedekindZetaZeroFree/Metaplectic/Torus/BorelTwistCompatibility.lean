module

public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaNormTransport
public import DedekindZetaZeroFree.Eisenstein.Induction.TwistedAveragingAndSmoothLevels

@[expose] public section

open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := KPGlobalTorusFunctionData.G F ζ hζ
abbrev E := KPGlobalTorusFunctionData.E F ζ hζ

abbrev ModelData := KPGlobalTorusPeriodizationInverse.ModelData F ζ hζ

abbrev Polarization := KPGlobalTorusFunctionData.Polarization F ζ hζ

def normPower (s : ℂ) (t : E F ζ hζ) : ℂ :=
  Complex.exp (s * (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) : ℂ))

theorem normPower_mul (s : ℂ) (a b : E F ζ hζ) :
    normPower F ζ hζ s (a * b) = normPower F ζ hζ s a * normPower F ζ hζ s b := by
  unfold normPower
  rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul]
  · simp only [Complex.ofReal_add, mul_add, Complex.exp_add]
  · exact_mod_cast Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ a)
  · exact_mod_cast Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ b)

 theorem normPower_neg (s : ℂ) (a : E F ζ hζ) :
    normPower F ζ hζ (-s) a = (normPower F ζ hζ s a)⁻¹ := by
  simp only [normPower, neg_mul, Complex.exp_neg]

 theorem normPower_continuous (s : ℂ) : Continuous (normPower F ζ hζ s) := by
  have hd : Continuous (fun t : E F ζ hζ =>
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ))) := by
    have h : (fun t : E F ζ hζ =>
        (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ))) =
        (fun t => (((KPGlobalCenterRationalCharacter.nu F ζ hζ t : ℝ≥0) : ℝ)) ^ 6) := by
      funext t
      simp only [KPGlobalCenterRationalCharacter.nu, MonoidHom.comp_apply,
        KPGlobalCenterRationalCharacter.sixthPower, Units.coe_map, NNReal.rpowMonoidHom_apply,
        NNReal.coe_rpow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _)]
      norm_num
    rw [h]
    exact (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))).pow 6
  have hn : ∀ t : E F ζ hζ,
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) ≠ 0 := by
    intro t
    exact_mod_cast Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t)
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (hd.log hn)))

def normCharacter (s : ℂ) : E F ζ hζ →ₜ* ℂˣ where
  toFun t := Units.mk0 (normPower F ζ hζ s t) (Complex.exp_ne_zero _)
  map_one' := by
    apply Units.val_injective
    change normPower F ζ hζ s 1 = 1
    simp [normPower]
  map_mul' := by
    intro a b
    apply Units.val_injective
    exact normPower_mul F ζ hζ s a b
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    constructor
    · exact normPower_continuous F ζ hζ s
    · change Continuous (fun t => (normPower F ζ hζ s t)⁻¹)
      simp only [← normPower_neg]
      exact normPower_continuous F ζ hζ (-s)

 theorem delta_rational (y : Fˣ) :
    KPGlobalTorusFunctionData.delta F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ y) = 1 := by
  apply Units.val_injective
  apply NNReal.rpow_left_injective (show (1 / 6 : ℝ) ≠ 0 by norm_num)
  change (KPGlobalCenterRationalCharacter.nu F ζ hζ
      (KPGlobalTorusFunctionData.s F ζ hζ y) : ℝ≥0) = (1 : ℝ≥0) ^ (1 / 6 : ℝ)
  rw [show KPGlobalCenterRationalCharacter.nu F ζ hζ
      (KPGlobalTorusFunctionData.s F ζ hζ y) = 1 from
    KPGlobalTorusPeriodizationInverse.rational_representative_norm F ζ hζ y]
  simp

 theorem normCharacter_rational (s : ℂ) (y : Fˣ) :
    normCharacter F ζ hζ s (KPGlobalTorusFunctionData.s F ζ hζ y) = 1 := by
  apply Units.val_injective
  change normPower F ζ hζ s (KPGlobalTorusFunctionData.s F ζ hζ y) = 1
  simp [normPower, delta_rational]

def twist (P : Polarization F ζ hζ) (s : ℂ) : Polarization F ζ hζ where
  H := P.H
  closed := P.closed
  abelian := P.abelian
  contains_center := P.contains_center
  character := P.character * (normCharacter F ζ hζ s).comp
    ⟨P.H.subtype, continuous_subtype_val⟩

abbrev Smooth (P : Polarization F ζ hζ) :=
  KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P

local instance smoothTopology (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

abbrev rationalModel := KPGlobalTorusPeriodizationInverse.rationalModel F ζ hζ

abbrev GroupArch := InfinitePlace F → Fin 3 → ℂ

def groupArchDomain : Set (GroupArch F) := {z | ∀ w, z w 1 ≠ 0}

def groupArchTuple (z : GroupArch F) : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ := by
  refine ⟨fun v => ?_, ?_⟩
  · cases v with
    | inl w =>
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)
      let y : w.Completionˣ := if h : z w 1 = 0 then 1
        else Units.mk0 (e.symm (z w 1)) (by
          intro h0
          apply h
          simpa using congrArg e h0)
      exact KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) (e.symm (z w 0)) *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) y *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (e.symm (z w 2))
    | inr q => exact 1
  · apply Filter.Eventually.of_forall
    intro v
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q => exact Subgroup.one_mem _

def groupArchChart (z : GroupArch F) : G F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (groupArchTuple F ζ hζ z))

 theorem groupArchDomain_open : IsOpen (groupArchDomain F) := by
  rw [groupArchDomain, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro w
  exact isOpen_ne_fun (show Continuous (fun z : GroupArch F => z w (1 : Fin 3)) by fun_prop)
    continuous_const

def InducedFunctions (P : Polarization F ζ hζ) :
    Submodule ℂ (G F ζ hζ → Smooth F ζ hζ P) where
  carrier := {f | ∀ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ),
    f ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ t •
        KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P t (f g)}
  zero_mem' := by
    intros
    simp
  add_mem' := by
    intro f k hf hk t x g
    simp only [Pi.add_apply, hf t x g, hk t x g, map_add, smul_add]
  smul_mem' := by
    intro c f hf t x g
    simp only [Pi.smul_apply, hf t x g, map_smul]
    exact smul_comm c _ _

def InducedLevel (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    Submodule ℂ (InducedFunctions F ζ hζ P) where
  carrier := {f | (∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val (groupArchChart F ζ hζ z * g)).val.val 1) (groupArchDomain F)) ∧
    ∀ (g : G F ζ hζ) (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      f.val (g * j.val) = f.val g}
  zero_mem' := by
    constructor
    · intro g; exact contDiffOn_const
    · intros; rfl
  add_mem' := by
    intro f k hf hk
    constructor
    · intro g; exact (hf.1 g).add (hk.1 g)
    · intro g j; change f.val (g * j.val) + k.val (g * j.val) = _
      rw [hf.2 g j, hk.2 g j]
      rfl
  smul_mem' := by
    intro c f hf
    constructor
    · intro g; exact contDiffOn_const.smul (hf.1 g)
    · intro g j; change c • f.val (g * j.val) = _
      rw [hf.2 g j]
      rfl

def Induced (P : Polarization F ζ hζ) : Submodule ℂ (InducedFunctions F ζ hζ P) :=
  ⨆ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ, InducedLevel F ζ hζ P J

local instance inducedFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) := @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)

local instance inducedLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

local instance inducedAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (Induced F ζ hζ P) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (Induced F ζ hζ P)

def inducedJetBound (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : InducedLevel F ζ hζ P J) : ℝ :=
  sSup ((fun z => ‖iteratedFDerivWithin ℝ n
    (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
    (groupArchDomain F) z‖) '' K.set)

theorem jet_image_bdd (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : InducedLevel F ζ hζ P J) :
    BddAbove ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set) := by
  apply K.compact.bddAbove_image
  apply ContinuousOn.mono _ K.inside
  exact ((f.property.1 g).continuousOn_iteratedFDerivWithin (by simp)
    (groupArchDomain_open F).uniqueDiffOn).norm

theorem inducedJetBound_add_le (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f h : InducedLevel F ζ hζ P J) :
    inducedJetBound F ζ hζ P J g n K (f + h) ≤
      inducedJetBound F ζ hζ P J g n K f + inducedJetBound F ζ hζ P J g n K h := by
  by_cases hK : K.set.Nonempty
  · apply csSup_le (hK.image _)
    rintro r ⟨z, hz, rfl⟩
    have hzU := K.inside hz
    change ‖iteratedFDerivWithin ℝ n
      ((fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1) +
       (fun y => (h.val.val (groupArchChart F ζ hζ y * g)).val.val 1))
      (groupArchDomain F) z‖ ≤ _
    rw [iteratedFDerivWithin_add_apply
      ((f.property.1 g z hzU).of_le (by simp))
      ((h.property.1 g z hzU).of_le (by simp))
      (groupArchDomain_open F).uniqueDiffOn hzU]
    exact (norm_add_le _ _).trans (add_le_add
      (le_csSup (jet_image_bdd F ζ hζ P J g n K f) (Set.mem_image_of_mem _ hz))
      (le_csSup (jet_image_bdd F ζ hζ P J g n K h) (Set.mem_image_of_mem _ hz)))
  · have hE : K.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
    simp [inducedJetBound, hE, Real.sSup_empty]

private theorem norm_jet_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} {v : V} {n : ℕ} {f : V → ℂ} (c : ℂ)
    (hf : ContDiffWithinAt ℝ n f s v) (hs : UniqueDiffOn ℝ s) (hv : v ∈ s) :
    ‖iteratedFDerivWithin ℝ n (c • f) s v‖ =
      ‖c‖ * ‖iteratedFDerivWithin ℝ n f s v‖ := by
  rw [iteratedFDerivWithin_const_smul_apply (R := ℂ) hf hs hv, norm_smul]

theorem inducedJetBound_smul (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (c : ℂ) (f : InducedLevel F ζ hζ P J) :
    inducedJetBound F ζ hζ P J g n K (c • f) = ‖c‖ * inducedJetBound F ζ hζ P J g n K f := by
  unfold inducedJetBound
  have hEq : (fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => ((c • f).val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set =
      ‖c‖ • ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set) := by
    change _ = (fun r : ℝ => ‖c‖ • r) '' ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set)
    rw [Set.image_image]
    apply Set.image_congr
    intro z hz
    change ‖iteratedFDerivWithin ℝ n
      (c • (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1))
      (groupArchDomain F) z‖ = ‖c‖ * ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖
    exact norm_jet_smul c
      ((f.property.1 g z (K.inside hz)).of_le (by simp))
      (groupArchDomain_open F).uniqueDiffOn (K.inside hz)
  rw [hEq]
  exact Real.sSup_smul_of_nonneg (α := ℝ) (norm_nonneg c) _

def inducedJet (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F)) :
    Seminorm ℂ (InducedLevel F ζ hζ P J) :=
  Seminorm.of (inducedJetBound F ζ hζ P J g n K)
    (inducedJetBound_add_le F ζ hζ P J g n K) (inducedJetBound_smul F ζ hζ P J g n K)

def inducedLevelTopology (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    TopologicalSpace (InducedLevel F ζ hζ P J) :=
  (SeminormFamily.moduleFilterBasis
    (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ P J i.1 i.2.1 i.2.2)).topology

def inducedStageInclusion (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] Induced F ζ hζ P :=
  Submodule.inclusion (le_iSup (fun J => InducedLevel F ζ hζ P J) J)

def inducedFinalSeminorms (P : Polarization F ζ hζ) :=
  {q : Seminorm ℂ (Induced F ζ hζ P) // ∀ J,
    @Continuous (InducedLevel F ζ hζ P J) ℝ
      (inducedLevelTopology F ζ hζ P J) inferInstance
      (q ∘ inducedStageInclusion F ζ hζ P J)}

def inducedTopology (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  (SeminormFamily.moduleFilterBasis
    (fun q : inducedFinalSeminorms F ζ hζ P => q.val)).topology

local instance inducedTop (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  inducedTopology F ζ hζ P

theorem finitePart_normal : (KPGlobalTorusFunctionData.finitePart F ζ hζ).Normal := by
  unfold KPGlobalTorusFunctionData.finitePart
  apply Subgroup.Normal.map (Subgroup.normal_iInf_normal fun w => inferInstance)
  change Function.Surjective (fun x => KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x))
  exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

def scalarSection (P : Polarization F ζ hζ) :
    Induced F ζ hζ P →ₗ[ℂ] KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P := by
  refine { toFun := fun f => ⟨fun g => (f.val.val g).val.val 1, ?_⟩
           map_add' := ?_
           map_smul' := ?_ }
  · rename_i f
    intro h x g
    have hf := f.val.property h.val x g
    have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hf
    change (f.val.val ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)).val.val 1 = _ at he
    change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
      (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P h.val (f.val.val g)).val.val 1 at he
    rw [KPGlobalTorusPeriodizationInverse.rightAction_formula, one_mul] at he
    change (f.val.val ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)).val.val 1 =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val * (P.character h : ℂ) *
        (f.val.val g).val.val 1
    rw [he]
    have hc := (f.val.val g).val.property h 1
    simp only [mul_one] at hc
    change _ * (f.val.val g).val.val h.val = _
    rw [hc]
    exact (mul_assoc _ _ _).symm
  · intros; rfl
  · intros; rfl

theorem scalarSection_formula (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) :
    (scalarSection F ζ hζ P f).val g = (f.val.val g).val.val 1 := by
  unfold scalarSection
  rfl

 theorem scalar_transitivity (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) (t : E F ζ hζ) :
    (f.val.val g).val.val t = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ *
      (scalarSection F ζ hζ P f).val (t.val * g) := by
  have hN : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hf := f.val.property t 0 g
  simp only [hN, mul_one] at hf
  have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hf
  change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ t *
    (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P t (f.val.val g)).val.val 1 at he
  rw [KPGlobalTorusPeriodizationInverse.rightAction_formula, one_mul] at he
  rw [scalarSection_formula, he]
  change _ = _⁻¹ * (_ * _)
  have hp : (0 : ℝ) < (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) := by
    exact_mod_cast (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t)) |> pos_iff_ne_zero.mpr
  have hn : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t ≠ 0 := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    exact_mod_cast (Real.sqrt_pos.2 hp).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

def levelRestriction (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] (K → Smooth F ζ hζ P) where
  toFun f k := f.val.val k.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def CompactLevel (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    Submodule ℂ (K → Smooth F ζ hζ P) := (levelRestriction F ζ hζ P J K).range

def restrictLevel (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] CompactLevel F ζ hζ P J K :=
  (levelRestriction F ζ hζ P J K).rangeRestrict

def compactLevelTopology (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    TopologicalSpace (CompactLevel F ζ hζ P J K) :=
  TopologicalSpace.coinduced (restrictLevel F ζ hζ P J K) (inducedLevelTopology F ζ hζ P J)

local instance compactTop (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    TopologicalSpace (CompactLevel F ζ hζ P J K) := compactLevelTopology F ζ hζ P J K

local instance inducedLevelTop (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    TopologicalSpace (InducedLevel F ζ hζ P J) := inducedLevelTopology F ζ hζ P J

def upperRoot (x : KPGlobalTorusFunctionData.Adeles F) :
    KPAdelicCoverRestrictedProduct.AdelicGL2 F :=
  Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x
private theorem upperRoot_entries (x : KPGlobalTorusFunctionData.Adeles F) (i j : Fin 2) :
    upperRoot F x i j = (!![1, x; 0, 1]) i j := by
  fin_cases i <;> fin_cases j <;> simp [upperRoot, Matrix.transvection]
private theorem adele_ext (a b : KPGlobalTorusFunctionData.Adeles F)
    (h : ∀ v, KPAdelicCoverRestrictedProduct.adeleEval F v a = KPAdelicCoverRestrictedProduct.adeleEval F v b) : a = b := by
  apply Prod.ext
  · funext w
    exact h (Sum.inl w)
  · apply Subtype.ext
    funext q
    exact h (Sum.inr q)
 theorem projected_root (x : KPGlobalTorusFunctionData.Adeles F) :
    KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (KPGlobalTorusFunctionData.N F ζ hζ x) =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) (upperRoot F x) := by
  change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
    (KPGlobalTorusFunctionData.rootTuple F ζ hζ x)) = _
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply adele_ext F
  intro v
  have h := KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ
    (KPGlobalTorusFunctionData.rootTuple F ζ hζ x) v
  have he := congrArg (fun A : KPLocalCover.LocalGL2 F v => A i j) h
  change KPAdelicCoverRestrictedProduct.adeleEval F v
    ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
      (KPGlobalTorusFunctionData.rootTuple F ζ hζ x)) i j) = _ at he
  rw [he]
  fin_cases i <;> fin_cases j <;>
    simp [KPGlobalTorusFunctionData.rootTuple, KPStandardLocalRootLifts.N,
      KPLocalCover.projection_apply, KPLocalCover.sectionMap, KubotaRankTwo.n,
      upperRoot_entries]
private theorem upper_unit {R : Type*} [CommRing R] (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0) :
    IsUnit (A 0 0) := by
  have h : IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) R)) :=
    (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := R) A).isUnit
  have hd : Matrix.det (A : Matrix (Fin 2) (Fin 2) R) = A 0 0 * A 1 1 := by
    simp only [Matrix.det_fin_two, h10, mul_zero, sub_zero]
  exact isUnit_of_mul_isUnit_left (hd ▸ h)
private theorem upper_diagonal {R : Type*} [CommRing R]
    (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0)
    (x : R) (hx : A 0 0 * x = A 0 1) :
    ((A * Matrix.GeneralLinearGroup.transvection (R := R) 0 1 (by decide) (-x) : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
    ((A * Matrix.GeneralLinearGroup.transvection (R := R) 0 1 (by decide) (-x) : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by
  constructor <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection, h10, hx]

 theorem actual_borel_factorization (b : KPGlobalTorusFunctionData.borel F ζ hζ) :
    ∃ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F),
      b.val = t.val * KPGlobalTorusFunctionData.N F ζ hζ x := by
  obtain ⟨A, hA, h10⟩ := b.property
  let u := (upper_unit A h10).unit
  let x : KPGlobalTorusFunctionData.Adeles F := ↑u⁻¹ * A 0 1
  have hx : A 0 0 * x = A 0 1 := by
    change A 0 0 * (↑u⁻¹ * A 0 1) = _
    have hu : (u : KPGlobalTorusFunctionData.Adeles F) = A 0 0 := (upper_unit A h10).unit_spec
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have ht : b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x) ∈ E F ζ hζ := by
    change ∃ D : KPAdelicCoverRestrictedProduct.AdelicGL2 F,
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) D =
        KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
          (b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x)) ∧ D 1 0 = 0 ∧ D 0 1 = 0
    refine ⟨A * upperRoot F (-x), ?_, upper_diagonal A h10 x hx⟩
    simp only [map_mul, projected_root, hA]
  refine ⟨⟨b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x), ht⟩, x, ?_⟩
  have hn : KPGlobalTorusFunctionData.N F ζ hζ (-x) * KPGlobalTorusFunctionData.N F ζ hζ x = 1 := by
    rw [← KPGlobalTorusFunctionData.N_add, neg_add_cancel]
    exact (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  change b.val = (b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x)) * KPGlobalTorusFunctionData.N F ζ hζ x
  rw [mul_assoc, hn, mul_one]

 theorem upper_units {R : Type*} [CommRing R]
    (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0) :
    IsUnit (A 0 0) ∧ IsUnit (A 1 1) := by
  have h : IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) R)) :=
    (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := R) A).isUnit
  have hd : Matrix.det (A : Matrix (Fin 2) (Fin 2) R) = A 0 0 * A 1 1 := by
    simp only [Matrix.det_fin_two, h10, mul_zero, sub_zero]
  exact ⟨isUnit_of_mul_isUnit_left (hd ▸ h), isUnit_of_mul_isUnit_right (hd ▸ h)⟩
 def ratio {R : Type*} [CommRing R]
    (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0) : Rˣ :=
  (upper_units A h10).1.unit * ((upper_units A h10).2.unit)⁻¹
private theorem upper_product {R : Type*} [CommRing R]
    (A B : Matrix.GeneralLinearGroup (Fin 2) R) (hA : A 1 0 = 0) (hB : B 1 0 = 0) :
    ((A * B : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB]
private theorem ratio_mul {R : Type*} [CommRing R]
    (A B : Matrix.GeneralLinearGroup (Fin 2) R) (hA : A 1 0 = 0) (hB : B 1 0 = 0) :
    ratio (A * B) (upper_product A B hA hB) = ratio A hA * ratio B hB := by
  have h0 : (upper_units (A * B) (upper_product A B hA hB)).1.unit =
      (upper_units A hA).1.unit * (upper_units B hB).1.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hB]
  have h1 : (upper_units (A * B) (upper_product A B hA hB)).2.unit =
      (upper_units A hA).2.unit * (upper_units B hB).2.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA]
  simp only [ratio, h0, h1]
  simp only [mul_inv_rev]; ac_rfl
private theorem ratio_eq (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hA : A 1 0 = 0) (hB : B 1 0 = 0)
    (h : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B) :
    ratio A hA = ratio B hB := by
  have hm := QuotientGroup.eq.mp h
  obtain ⟨z, hz⟩ := hm
  have he : B = A * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
    change Matrix.GeneralLinearGroup.scalar (Fin 2) z = A⁻¹ * B at hz
    rw [hz]
    group
  have h0 : (upper_units B hB).1.unit = (upper_units A hA).1.unit * z := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    rw [he]
    simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar]
  have h1 : (upper_units B hB).2.unit = (upper_units A hA).2.unit * z := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    rw [he]
    simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar]
  simp only [ratio, h0, h1]
  simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

private theorem root_upper (x : KPGlobalTorusFunctionData.Adeles F) :
    upperRoot F x 1 0 = 0 := by rw [upperRoot_entries]; rfl

 def borelRatio (b : KPGlobalTorusFunctionData.borel F ζ hζ) : KPGlobalTorusFunctionData.Ideles F :=
  ratio (Classical.choose b.property) (Classical.choose_spec b.property).2

private theorem borelRatio_formula (b : KPGlobalTorusFunctionData.borel F ζ hζ)
    (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ b.val) (h10 : A 1 0 = 0) :
    borelRatio F ζ hζ b = ratio A h10 := by
  apply ratio_eq F
  exact (Classical.choose_spec b.property).1.trans hA.symm

 theorem borelRatio_mul (b c : KPGlobalTorusFunctionData.borel F ζ hζ) :
    borelRatio F ζ hζ (b * c) = borelRatio F ζ hζ b * borelRatio F ζ hζ c := by
  let A := Classical.choose b.property
  let B := Classical.choose c.property
  have hA := Classical.choose_spec b.property
  have hB := Classical.choose_spec c.property
  rw [borelRatio_formula F ζ hζ (b * c) (A * B) (by
    change _ = KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (b.val * c.val)
    exact (map_mul _ A B).trans ((congrArg₂ (fun a b => a * b) hA.1 hB.1).trans (map_mul _ b.val c.val).symm)) (upper_product A B hA.2 hB.2)]
  exact ratio_mul A B hA.2 hB.2

 theorem borel_torus (t : E F ζ hζ) : t.val ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  exact ⟨A, hA, h10⟩

 theorem borel_root (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.N F ζ hζ x ∈ KPGlobalTorusFunctionData.borel F ζ hζ :=
  ⟨upperRoot F x, (projected_root F ζ hζ x).symm, root_upper F x⟩

 def borelElement (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.borel F ζ hζ :=
  ⟨t.val * KPGlobalTorusFunctionData.N F ζ hζ x,
    Subgroup.mul_mem _ (borel_torus F ζ hζ t) (borel_root F ζ hζ x)⟩

 theorem borelRatio_torus (t : E F ζ hζ) :
    borelRatio F ζ hζ ⟨t.val, borel_torus F ζ hζ t⟩ = KPGlobalTorusFunctionData.p F ζ hζ t := by
  let A := Classical.choose t.property
  have hA := Classical.choose_spec t.property
  rw [borelRatio_formula F ζ hζ _ A hA.1 hA.2.1]
  apply Units.ext
  have hh := KPGlobalTorusFunctionData.ratio_formula F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩ A hA.1 hA.2.1 hA.2.2
  change (ratio A hA.2.1 : KPGlobalTorusFunctionData.Adeles F) =
    ((KPGlobalTorusFunctionData.torusRatio F)
      ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩ : KPGlobalTorusFunctionData.Adeles F)
  rw [hh]
  unfold ratio
  simp only [Units.val_mul]

private theorem borelRatio_root (x : KPGlobalTorusFunctionData.Adeles F) :
    borelRatio F ζ hζ ⟨KPGlobalTorusFunctionData.N F ζ hζ x, borel_root F ζ hζ x⟩ = 1 := by
  rw [borelRatio_formula F ζ hζ _ (upperRoot F x) (projected_root F ζ hζ x).symm (root_upper F x)]
  have h0 : (upper_units (upperRoot F x) (root_upper F x)).1.unit = 1 := by
    apply Units.ext
    simp only [IsUnit.unit_spec, upperRoot_entries, Units.val_one]
    rfl
  have h1 : (upper_units (upperRoot F x) (root_upper F x)).2.unit = 1 := by
    apply Units.ext
    simp only [IsUnit.unit_spec, upperRoot_entries, Units.val_one]
    rfl
  simp only [ratio, h0, h1, inv_one, mul_one]

private theorem borelRatio_element (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) :
    borelRatio F ζ hζ (borelElement F ζ hζ t x) = KPGlobalTorusFunctionData.p F ζ hζ t := by
  change borelRatio F ζ hζ (⟨t.val, borel_torus F ζ hζ t⟩ *
    ⟨KPGlobalTorusFunctionData.N F ζ hζ x, borel_root F ζ hζ x⟩) = _
  rw [borelRatio_mul, borelRatio_torus, borelRatio_root, mul_one]

 def borelRatioHom : KPGlobalTorusFunctionData.borel F ζ hζ →* KPGlobalTorusFunctionData.Ideles F where
  toFun := borelRatio F ζ hζ
  map_one' := by
    have h := borelRatio_torus F ζ hζ 1
    have he : (⟨(1 : E F ζ hζ).val, borel_torus F ζ hζ 1⟩ : KPGlobalTorusFunctionData.borel F ζ hζ) = 1 := Subtype.ext rfl
    rw [he, map_one] at h
    exact h
  map_mul' := borelRatio_mul F ζ hζ

 def borelDelta : KPGlobalTorusFunctionData.borel F ζ hζ →* (ℝ≥0)ˣ :=
  (KPGlobalTorusFunctionData.ideleAbs F).comp (borelRatioHom F ζ hζ)

private theorem borelDelta_element (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) :
    borelDelta F ζ hζ (borelElement F ζ hζ t x) = KPGlobalTorusFunctionData.delta F ζ hζ t := by
  change KPGlobalTorusFunctionData.ideleAbs F (borelRatio F ζ hζ (borelElement F ζ hζ t x)) = _
  rw [borelRatio_element]
  rfl

structure IwasawaData where
  K : Subgroup (G F ζ hζ)
  compact : IsCompact (K : Set (G F ζ hζ))
  decomposition : ∀ g : G F ζ hζ,
    ∃ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (k : K),
      g = (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val
  overlap : ∀ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F),
    t.val * KPGlobalTorusFunctionData.N F ζ hζ x ∈ K →
      KPGlobalTorusFunctionData.delta F ζ hζ t = 1

def iwasawaNorm (D : IwasawaData F ζ hζ) (g : G F ζ hζ) : (ℝ≥0)ˣ :=
  KPGlobalTorusFunctionData.delta F ζ hζ (Classical.choose (D.decomposition g))

 theorem iwasawaNorm_formula (D : IwasawaData F ζ hζ)
    (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (k : D.K) :
    iwasawaNorm F ζ hζ D ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val) =
      KPGlobalTorusFunctionData.delta F ζ hζ t := by
  let g := (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val
  let u := Classical.choose (D.decomposition g)
  let y := Classical.choose (Classical.choose_spec (D.decomposition g))
  let l := Classical.choose (Classical.choose_spec (Classical.choose_spec (D.decomposition g)))
  have hl : g = (u.val * KPGlobalTorusFunctionData.N F ζ hζ y) * l.val :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (D.decomposition g)))
  let b := borelElement F ζ hζ u y
  let c := borelElement F ζ hζ t x
  have he : (b⁻¹ * c).val = l.val * k.val⁻¹ := by
    have h : c.val * k.val = b.val * l.val := hl
    change b.val⁻¹ * c.val = _
    calc
      b.val⁻¹ * c.val = b.val⁻¹ * ((c.val * k.val) * k.val⁻¹) := by group
      _ = b.val⁻¹ * ((b.val * l.val) * k.val⁻¹) := by rw [h]
      _ = l.val * k.val⁻¹ := by group
  obtain ⟨v, z, hv⟩ := actual_borel_factorization F ζ hζ (b⁻¹ * c)
  have hK : v.val * KPGlobalTorusFunctionData.N F ζ hζ z ∈ D.K := by
    rw [← hv, he]
    exact D.K.mul_mem l.property (D.K.inv_mem k.property)
  have hd : borelDelta F ζ hζ (b⁻¹ * c) = 1 := by
    have hb : b⁻¹ * c = borelElement F ζ hζ v z := Subtype.ext hv
    rw [hb, borelDelta_element]
    exact D.overlap v z hK
  rw [map_mul, map_inv] at hd
  have hb := borelDelta_element F ζ hζ u y
  have hc := borelDelta_element F ζ hζ t x
  change (borelDelta F ζ hζ b)⁻¹ * borelDelta F ζ hζ c = 1 at hd
  rw [hb, hc] at hd
  change KPGlobalTorusFunctionData.delta F ζ hζ u = KPGlobalTorusFunctionData.delta F ζ hζ t
  exact inv_mul_eq_one.mp hd

theorem iwasawaNorm_right_compact (D : IwasawaData F ζ hζ)
    (g : G F ζ hζ) (k : D.K) :
    iwasawaNorm F ζ hζ D (g * k.val) = iwasawaNorm F ζ hζ D g := by
  obtain ⟨t, x, l, rfl⟩ := D.decomposition g
  have he : ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * l.val) * k.val =
      (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * (l * k).val := by
    simp [mul_assoc]
  rw [he, iwasawaNorm_formula, iwasawaNorm_formula]

theorem iwasawaNorm_borel_mul (D : IwasawaData F ζ hζ)
    (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    iwasawaNorm F ζ hζ D ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.delta F ζ hζ t * iwasawaNorm F ζ hζ D g := by
  obtain ⟨u, y, k, rfl⟩ := D.decomposition g
  let b := borelElement F ζ hζ t x * borelElement F ζ hζ u y
  obtain ⟨v, z, hv⟩ := actual_borel_factorization F ζ hζ b
  have hd : KPGlobalTorusFunctionData.delta F ζ hζ v =
      KPGlobalTorusFunctionData.delta F ζ hζ t * KPGlobalTorusFunctionData.delta F ζ hζ u := by
    have hb : b = borelElement F ζ hζ v z := Subtype.ext hv
    have hm := (borelDelta F ζ hζ).map_mul (borelElement F ζ hζ t x) (borelElement F ζ hζ u y)
    change borelDelta F ζ hζ b = _ at hm
    rw [hb, borelDelta_element, borelDelta_element, borelDelta_element] at hm
    exact hm
  have he : (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) *
      ((u.val * KPGlobalTorusFunctionData.N F ζ hζ y) * k.val) =
      (v.val * KPGlobalTorusFunctionData.N F ζ hζ z) * k.val := by
    rw [← hv]
    change _ = ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) *
      (u.val * KPGlobalTorusFunctionData.N F ζ hζ y)) * k.val
    exact (mul_assoc _ _ _).symm
  rw [he, iwasawaNorm_formula, iwasawaNorm_formula, hd]

theorem iwasawaNorm_compact (D : IwasawaData F ζ hζ) (k : D.K) :
    iwasawaNorm F ζ hζ D k.val = 1 := by
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have h := iwasawaNorm_formula F ζ hζ D 1 0 k
  simpa [hn] using h

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility

section

open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] smoothTopology inducedFunctionsAddGroup inducedLevelAddGroup
  inducedAddGroup inducedTop compactTop inducedLevelTop

 theorem normPower_entire (t : E F ζ hζ) :
    Differentiable ℂ (fun s => normPower F ζ hζ s t) := by
  exact Complex.differentiable_exp.comp (differentiable_id.mul_const _)

def normTwist (P : Polarization F ζ hζ) (s : ℂ) :
    Smooth F ζ hζ P ≃L[ℂ] Smooth F ζ hζ (twist F ζ hζ P s) := by
  exact KPGlobalTorusBorelNormTwistTransport.normTwist F ζ hζ P s

 theorem normTwist_formula (P : Polarization F ζ hζ) (s : ℂ)
    (f : Smooth F ζ hζ P) (t : E F ζ hζ) :
    (normTwist F ζ hζ P s f).val.val t = normPower F ζ hζ s t * f.val.val t := by
  exact KPGlobalTorusBorelNormTwistTransport.normTwist_formula F ζ hζ P s f t

 theorem normTwist_inverse_formula (P : Polarization F ζ hζ) (s : ℂ)
    (f : Smooth F ζ hζ (twist F ζ hζ P s)) (t : E F ζ hζ) :
    ((normTwist F ζ hζ P s).symm f).val.val t =
      normPower F ζ hζ (-s) t * f.val.val t := by
  have hf := normTwist_formula F ζ hζ P s ((normTwist F ζ hζ P s).symm f) t
  rw [ContinuousLinearEquiv.apply_symm_apply] at hf
  rw [normPower_neg, hf]
  have hn : normPower F ζ hζ s t ≠ 0 := Complex.exp_ne_zero _
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

private theorem normTwist_rightAction (P : Polarization F ζ hζ) (s : ℂ)
    (a : E F ζ hζ) (f : Smooth F ζ hζ P) :
    KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ (twist F ζ hζ P s) a
        (normTwist F ζ hζ P s f) =
      normPower F ζ hζ s a • normTwist F ζ hζ P s
        (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P a f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change _ = normPower F ζ hζ s a * _
  simp only [KPGlobalTorusPeriodizationInverse.rightAction_formula, normTwist_formula,
    normPower_mul]
  ring

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
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [KPGlobalTorusPeriodizationInverse.periodization_averaging F ζ hζ C]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

 theorem twistedQ_twistedP (C : ModelData F ζ hζ) (s : ℂ) (f : Product F ζ hζ C s) :
    twistedQ F ζ hζ C s (twistedP F ζ hζ C s f) = f := by
  simp only [twistedP, twistedQ, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [KPGlobalTorusPeriodizationInverse.averaging_periodization F ζ hζ C]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

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
    simp [KPGlobalTorusPeriodizationInverse.rationalLift, normPower, delta_rational]
  rw [hn, one_mul, normPower_neg]
  have ht : normPower F ζ hζ s t ≠ 0 := Complex.exp_ne_zero _
  rw [← mul_assoc, mul_inv_cancel₀ ht, one_mul]

def twistedIntegrand (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ)
    (x : KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C) : ℂ :=
  (((twist F ζ hζ (productModel F ζ hζ C) s).character (r.lift x))⁻¹ : ℂˣ) *
    f.val.val ((r.lift x).val * t)

private theorem twistedIntegrand_transport (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ)
    (x : KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C) :
    twistedIntegrand F ζ hζ C s r f t x = normPower F ζ hζ s t *
      KPGlobalTorusPeriodizationInverse.averagingIntegrand F ζ hζ C r
        ((normTwist F ζ hζ (rationalModel F ζ hζ) s).symm f) t x := by
  have hf := normTwist_formula F ζ hζ (rationalModel F ζ hζ) s
    ((normTwist F ζ hζ (rationalModel F ζ hζ) s).symm f) ((r.lift x).val * t)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hf
  unfold twistedIntegrand KPGlobalTorusPeriodizationInverse.averagingIntegrand
  rw [hf, normPower_mul]
  simp only [twist]
  unfold normCharacter
  change ((((productModel F ζ hζ C).character (r.lift x) *
      Units.mk0 (normPower F ζ hζ s (r.lift x).val) (Complex.exp_ne_zero _))⁻¹ : ℂˣ) : ℂ) * _ = _
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hn := Complex.exp_ne_zero
    (s * (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ (r.lift x).val : ℝ≥0) : ℝ)) : ℂ))
  change normPower F ζ hζ s (r.lift x).val ≠ 0 at hn
  field_simp
  simp only [productModel, KPGlobalTorusPeriodizationInverse.productModel]
  change normPower F ζ hζ s (r.lift x).val * normPower F ζ hζ s t *
      ((normTwist F ζ hζ (rationalModel F ζ hζ) s).symm f).val.val ((r.lift x).val * t) * _ =
    normPower F ζ hζ s (r.lift x).val * _ * normPower F ζ hζ s t *
      ((normTwist F ζ hζ (rationalModel F ζ hζ) s).symm f).val.val ((r.lift x).val * t)
  ring_nf
  rfl

 theorem twistedIntegrand_independent (C : ModelData F ζ hζ) (s : ℂ)
    (r r' : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ) :
    twistedIntegrand F ζ hζ C s r f t = twistedIntegrand F ζ hζ C s r' f t := by
  funext x
  simp only [twistedIntegrand_transport]
  rw [KPGlobalTorusPeriodizationInverse.averagingIntegrand_independent F ζ hζ C r r']

 theorem twistedIntegrand_integrable (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ) :
    Integrable (twistedIntegrand F ζ hζ C s r f t)
      (KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C) := by
  have he : twistedIntegrand F ζ hζ C s r f t = (fun x => normPower F ζ hζ s t *
      KPGlobalTorusPeriodizationInverse.averagingIntegrand F ζ hζ C r
        ((normTwist F ζ hζ (rationalModel F ζ hζ) s).symm f) t x) := by
    funext x
    exact twistedIntegrand_transport F ζ hζ C s r f t x
  rw [he]
  exact (KPGlobalTorusPeriodizationInverse.averagingIntegrand_integrable F ζ hζ C r
    ((normTwist F ζ hζ (rationalModel F ζ hζ) s).symm f) t).const_mul _

 theorem twistedQ_formula (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : Rational F ζ hζ s) (t : E F ζ hζ) :
    (twistedQ F ζ hζ C s f).val.val t =
      ∫ x, twistedIntegrand F ζ hζ C s r f t
        x ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C := by
  simp only [twistedQ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    normTwist_formula, twistedIntegrand_transport]
  rw [KPGlobalTorusPeriodizationInverse.averaging_formula F ζ hζ C r, integral_const_mul]

def borelP (C : ModelData F ζ hζ) (s : ℂ) :
    Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) →L[ℂ]
      Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) := by
  exact KPGlobalTorusBorelNormTwistTransport.borelP F ζ hζ C s

def borelQ (C : ModelData F ζ hζ) (s : ℂ) :
    Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) →L[ℂ]
      Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) := by
  exact KPGlobalTorusBorelNormTwistTransport.borelQ F ζ hζ C s

 theorem borelP_fiberwise (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) (g : G F ζ hζ) :
    (borelP F ζ hζ C s f).val.val g = twistedP F ζ hζ C s (f.val.val g) := by
  exact KPGlobalTorusBorelNormTwistTransport.borelP_fiberwise F ζ hζ C s f g

 theorem borelQ_fiberwise (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) (g : G F ζ hζ) :
    (borelQ F ζ hζ C s f).val.val g = twistedQ F ζ hζ C s (f.val.val g) := by
  exact KPGlobalTorusBorelNormTwistTransport.borelQ_fiberwise F ζ hζ C s f g

 theorem borelP_borelQ (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) :
    borelP F ζ hζ C s (borelQ F ζ hζ C s f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [borelP_fiberwise, borelQ_fiberwise, twistedP_twistedQ]

 theorem borelQ_borelP (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    borelQ F ζ hζ C s (borelP F ζ hζ C s f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [borelQ_fiberwise, borelP_fiberwise, twistedQ_twistedP]

private def finiteConj (a : G F ζ hζ) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  refine ⟨(MulAut.conjNormal a).toEquiv, ?_, ?_⟩
  · apply Continuous.subtype_mk
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => a * x.val * a⁻¹)
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  · apply Continuous.subtype_mk
    have he : (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a).symm = MulAut.conjNormal a⁻¹ := by
      change (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a)⁻¹ = _
      rw [map_inv]
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => ((MulAut.conjNormal a).symm x).val)
    rw [he]
    simp only [MulAut.conjNormal_apply, inv_inv]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

private def conjLevel (a : G F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.FiniteLevel F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  exact ⟨J.toOpenSubgroup.comap (MulAut.conjNormal a⁻¹).toMonoidHom (by
      change Continuous (finiteConj F ζ hζ a⁻¹)
      exact (finiteConj F ζ hζ a⁻¹).continuous),
    (finiteConj F ζ hζ a⁻¹).isCompact_preimage.mpr J.isCompact⟩

 def inducedFunctionsTranslation (P : Polarization F ζ hζ) :
    Representation ℂ (G F ζ hζ) (InducedFunctions F ζ hζ P) where
  toFun a :=
    { toFun := fun f => ⟨fun g => f.val (g * a), by
        intro t x g
        simpa only [mul_assoc] using f.property t x (g * a)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f g; simp
  map_mul' := by intros; ext f g; simp [mul_assoc]

private theorem induced_translate_level (P : Polarization F ζ hζ)
    (a : G F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (hf : f ∈ InducedLevel F ζ hζ P J) :
    inducedFunctionsTranslation F ζ hζ P a f ∈
      InducedLevel F ζ hζ P (conjLevel F ζ hζ a J) := by
  constructor
  · intro g
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val ((groupArchChart F ζ hζ z * g) * a)).val.val 1) _
    simpa only [mul_assoc] using hf.1 (g * a)
  · intro g j
    have hj : a⁻¹ * j.val * a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
      obtain ⟨k, hk, he⟩ := j.property
      have hk' : a⁻¹ * k.val * a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
        letI := finitePart_normal F ζ hζ
        apply Subgroup.mem_map.mpr
        exact ⟨MulAut.conjNormal a⁻¹ k, hk, by simp only [Subgroup.subtype_apply, MulAut.conjNormal_apply, inv_inv]⟩
      change k.val = j.val at he
      rw [← he]
      exact hk'
    have hh := hf.2 (g * a) ⟨a⁻¹ * j.val * a, hj⟩
    change f.val ((g * j.val) * a) = f.val (g * a)
    have he : (g * a) * (a⁻¹ * j.val * a) = (g * j.val) * a := by group
    change f.val ((g * a) * (a⁻¹ * j.val * a)) = f.val (g * a) at hh
    rwa [he] at hh

 theorem induced_translate_union (P : Polarization F ζ hζ) (a : G F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (hf : f ∈ Induced F ζ hζ P) :
    inducedFunctionsTranslation F ζ hζ P a f ∈ Induced F ζ hζ P := by
  have hle : Induced F ζ hζ P ≤ (Induced F ζ hζ P).comap
      (inducedFunctionsTranslation F ζ hζ P a) := by
    apply iSup_le
    intro J x hx
    exact Submodule.mem_iSup_of_mem (conjLevel F ζ hζ a J)
      (induced_translate_level F ζ hζ P a J x hx)
  exact hle hf

def inducedRightAction (P : Polarization F ζ hζ) :
    Representation ℂ (G F ζ hζ) (Induced F ζ hζ P) where
  toFun a := (inducedFunctionsTranslation F ζ hζ P a).restrict
    (induced_translate_union F ζ hζ P a)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val (g * 1) = f.val.val g
    exact congrArg f.val.val (mul_one g)
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val (g * (a * b)) = f.val.val ((g * a) * b)
    exact congrArg f.val.val (mul_assoc g a b).symm

 theorem inducedRightAction_formula (P : Polarization F ζ hζ)
    (a g : G F ζ hζ) (f : Induced F ζ hζ P) :
    (inducedRightAction F ζ hζ P a f).val.val g = f.val.val (g * a) := by rfl

 theorem borelP_intertwines (C : ModelData F ζ hζ) (s : ℂ) (a : G F ζ hζ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    borelP F ζ hζ C s
        (inducedRightAction F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) a f) =
      inducedRightAction F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) a
        (borelP F ζ hζ C s f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  simp only [borelP_fiberwise, inducedRightAction_formula]

 theorem borelQ_intertwines (C : ModelData F ζ hζ) (s : ℂ) (a : G F ζ hζ)
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) :
    borelQ F ζ hζ C s
        (inducedRightAction F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) a f) =
      inducedRightAction F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) a
        (borelQ F ζ hζ C s f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  simp only [borelQ_fiberwise, inducedRightAction_formula]

 theorem induced_smooth (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val.val (groupArchChart F ζ hζ z * g)).val.val 1)
      (groupArchDomain F) := by
  have hf := f.property
  change f.val ∈ ⨆ J, InducedLevel F ζ hζ P J at hf
  exact Submodule.iSup_induction (motive := fun x : InducedFunctions F ζ hζ P =>
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (x.val (groupArchChart F ζ hζ z * g)).val.val 1)
      (groupArchDomain F)) (fun J => InducedLevel F ζ hζ P J) hf
      (fun J x hx => hx.1 g) contDiffOn_const (fun x y hx hy => hx.add hy)

 theorem induced_mem_level (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (f : Induced F ζ hζ P)
    (hf : ∀ (g : G F ζ hζ) (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      f.val.val (g * j.val) = f.val.val g) :
    f.val ∈ InducedLevel F ζ hζ P J :=
  ⟨induced_smooth F ζ hζ P f, hf⟩

 def inducedLevelMap (P Q : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (m : Induced F ζ hζ P →ₗ[ℂ] Induced F ζ hζ Q)
    (hm : ∀ f : InducedLevel F ζ hζ P J, ∀ (g : G F ζ hζ)
      (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      (m (inducedStageInclusion F ζ hζ P J f)).val.val (g * j.val) =
      (m (inducedStageInclusion F ζ hζ P J f)).val.val g) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] InducedLevel F ζ hζ Q J :=
  ((Induced F ζ hζ Q).subtype.comp (m.comp (inducedStageInclusion F ζ hζ P J))).codRestrict
    (InducedLevel F ζ hζ Q J) (fun f =>
      induced_mem_level F ζ hζ Q J (m (inducedStageInclusion F ζ hζ P J f)) (hm f))

def borelPLevel (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J →ₗ[ℂ]
      InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J :=
  inducedLevelMap F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)
    (twist F ζ hζ (rationalModel F ζ hζ) s) J (borelP F ζ hζ C s).toLinearMap (by
    intro f g j
    let f' := inducedStageInclusion F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J f
    exact (borelP_fiberwise F ζ hζ C s f' (g * j.val)).trans
      ((congrArg (twistedP F ζ hζ C s) (f.property.2 g j)).trans
        (borelP_fiberwise F ζ hζ C s f' g).symm))

def borelQLevel (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J →ₗ[ℂ]
      InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J :=
  inducedLevelMap F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)
    (twist F ζ hζ (productModel F ζ hζ C) s) J (borelQ F ζ hζ C s).toLinearMap (by
    intro f g j
    let f' := inducedStageInclusion F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J f
    exact (borelQ_fiberwise F ζ hζ C s f' (g * j.val)).trans
      ((congrArg (twistedQ F ζ hζ C s) (f.property.2 g j)).trans
        (borelQ_fiberwise F ζ hζ C s f' g).symm))

 theorem borelPLevel_formula (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J) (g : G F ζ hζ) :
    (borelPLevel F ζ hζ C s J f).val.val g = twistedP F ζ hζ C s (f.val.val g) := by
  exact borelP_fiberwise F ζ hζ C s
    (inducedStageInclusion F ζ hζ _ J f) g

 theorem borelQLevel_formula (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J) (g : G F ζ hζ) :
    (borelQLevel F ζ hζ C s J f).val.val g = twistedQ F ζ hζ C s (f.val.val g) := by
  exact borelQ_fiberwise F ζ hζ C s
    (inducedStageInclusion F ζ hζ _ J f) g

theorem inducedStageContinuous (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    @Continuous _ _ (inducedLevelTopology F ζ hζ P J) (inducedTopology F ζ hζ P)
      (inducedStageInclusion F ζ hζ P J) := by
  letI := inducedLevelTopology F ζ hζ P J
  have hp : WithSeminorms (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ P J i.1 i.2.1 i.2.2) := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  have hq : WithSeminorms (fun q : inducedFinalSeminorms F ζ hζ P => q.val) := ⟨rfl⟩
  apply Seminorm.continuous_of_continuous_comp
    (𝕝 := ℂ) (𝕝₂ := ℂ) (τ₁₂ := RingHom.id ℂ) hq
    (inducedStageInclusion F ζ hζ P J)
  intro q
  exact q.property J

private def unionJetBound (P : Polarization F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : Induced F ζ hζ P) : ℝ :=
  sSup ((fun z => ‖iteratedFDerivWithin ℝ n
    (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
    (groupArchDomain F) z‖) '' K.set)

private theorem unionJet_bdd (P : Polarization F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : Induced F ζ hζ P) :
    BddAbove ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set) := by
  apply K.compact.bddAbove_image
  apply ContinuousOn.mono _ K.inside
  exact ((induced_smooth F ζ hζ P f g).continuousOn_iteratedFDerivWithin (by simp)
    (groupArchDomain_open F).uniqueDiffOn).norm

private theorem unionJet_add (P : Polarization F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f h : Induced F ζ hζ P) :
    unionJetBound F ζ hζ P g n K (f + h) ≤
      unionJetBound F ζ hζ P g n K f + unionJetBound F ζ hζ P g n K h := by
  by_cases hK : K.set.Nonempty
  · apply csSup_le (hK.image _)
    rintro r ⟨z, hz, rfl⟩
    have hzU := K.inside hz
    change ‖iteratedFDerivWithin ℝ n
      ((fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1) +
       (fun y => (h.val.val (groupArchChart F ζ hζ y * g)).val.val 1))
      (groupArchDomain F) z‖ ≤ _
    rw [iteratedFDerivWithin_add_apply
      ((induced_smooth F ζ hζ P f g z hzU).of_le (by simp))
      ((induced_smooth F ζ hζ P h g z hzU).of_le (by simp))
      (groupArchDomain_open F).uniqueDiffOn hzU]
    exact (norm_add_le _ _).trans (add_le_add
      (le_csSup (unionJet_bdd F ζ hζ P g n K f) (Set.mem_image_of_mem _ hz))
      (le_csSup (unionJet_bdd F ζ hζ P g n K h) (Set.mem_image_of_mem _ hz)))
  · have hE : K.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
    simp [unionJetBound, hE, Real.sSup_empty]

private theorem norm_union_jet_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} {v : V} {n : ℕ} {f : V → ℂ} (c : ℂ)
    (hf : ContDiffWithinAt ℝ n f s v) (hs : UniqueDiffOn ℝ s) (hv : v ∈ s) :
    ‖iteratedFDerivWithin ℝ n (c • f) s v‖ =
      ‖c‖ * ‖iteratedFDerivWithin ℝ n f s v‖ := by
  rw [iteratedFDerivWithin_const_smul_apply (R := ℂ) hf hs hv, norm_smul]

private theorem unionJet_smul (P : Polarization F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (c : ℂ) (f : Induced F ζ hζ P) :
    unionJetBound F ζ hζ P g n K (c • f) = ‖c‖ * unionJetBound F ζ hζ P g n K f := by
  unfold unionJetBound
  have hEq : (fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => ((c • f).val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set =
      ‖c‖ • ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set) := by
    change _ = (fun r : ℝ => ‖c‖ • r) '' ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set)
    rw [Set.image_image]
    apply Set.image_congr
    intro z hz
    change ‖iteratedFDerivWithin ℝ n
      (c • (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1))
      (groupArchDomain F) z‖ = ‖c‖ * ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖
    exact norm_union_jet_smul c
      ((induced_smooth F ζ hζ P f g z (K.inside hz)).of_le (by simp))
      (groupArchDomain_open F).uniqueDiffOn (K.inside hz)
  rw [hEq]
  exact Real.sSup_smul_of_nonneg (α := ℝ) (norm_nonneg c) _

private def unionJet (P : Polarization F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F)) :
    Seminorm ℂ (Induced F ζ hζ P) :=
  Seminorm.of (unionJetBound F ζ hζ P g n K)
    (unionJet_add F ζ hζ P g n K) (unionJet_smul F ζ hζ P g n K)

private theorem unionJet_continuous (P : Polarization F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F)) :
    Continuous (unionJet F ζ hζ P g n K) := by
  have hp : WithSeminorms (fun q : inducedFinalSeminorms F ζ hζ P => q.val) := ⟨rfl⟩
  apply hp.continuous_seminorm ⟨unionJet F ζ hζ P g n K, ?_⟩
  intro J
  letI := inducedLevelTopology F ζ hζ P J
  have hJ : WithSeminorms (fun i : G F ζ hζ × ℕ ×
      KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ P J i.1 i.2.1 i.2.2) := ⟨rfl⟩
  exact hJ.continuous_seminorm (g, n, K)

private theorem levelMap_continuous (P Q : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (m : Induced F ζ hζ P →L[ℂ] Induced F ζ hζ Q)
    (l : InducedLevel F ζ hζ P J →ₗ[ℂ] InducedLevel F ζ hζ Q J)
    (hl : ∀ f, inducedStageInclusion F ζ hζ Q J (l f) =
      m (inducedStageInclusion F ζ hζ P J f)) :
    @Continuous _ _ (inducedLevelTopology F ζ hζ P J)
      (inducedLevelTopology F ζ hζ Q J) l := by
  letI := inducedLevelTopology F ζ hζ P J
  letI := inducedLevelTopology F ζ hζ Q J
  have hp : WithSeminorms (fun i : G F ζ hζ × ℕ ×
      KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ P J i.1 i.2.1 i.2.2) := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  have hq : WithSeminorms (fun i : G F ζ hζ × ℕ ×
      KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ Q J i.1 i.2.1 i.2.2) := ⟨rfl⟩
  apply WithSeminorms.continuous_of_continuous_comp hq l
  intro i
  have he : (inducedJet F ζ hζ Q J i.1 i.2.1 i.2.2).comp l =
      unionJet F ζ hζ Q i.1 i.2.1 i.2.2 ∘ m ∘ inducedStageInclusion F ζ hζ P J := by
    funext f
    change unionJet F ζ hζ Q i.1 i.2.1 i.2.2
      (inducedStageInclusion F ζ hζ Q J (l f)) = _
    exact congrArg (unionJet F ζ hζ Q i.1 i.2.1 i.2.2) (hl f)
  rw [he]
  exact (unionJet_continuous F ζ hζ Q i.1 i.2.1 i.2.2).comp
    (m.continuous.comp (inducedStageContinuous F ζ hζ P J))

 theorem borelPLevel_continuous (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    @Continuous _ _
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (borelPLevel F ζ hζ C s J) := by
  apply levelMap_continuous F ζ hζ _ _ J (borelP F ζ hζ C s)
  intro f
  apply Subtype.ext
  apply Subtype.ext
  rfl

 theorem borelQLevel_continuous (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    @Continuous _ _
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (borelQLevel F ζ hζ C s J) := by
  apply levelMap_continuous F ζ hζ _ _ J (borelQ F ζ hζ C s)
  intro f
  apply Subtype.ext
  apply Subtype.ext
  rfl

def compactP (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    CompactLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K →L[ℂ]
      CompactLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K := by
  let m : CompactLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K →ₗ[ℂ]
      CompactLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K :=
    { toFun := fun f => ⟨fun k => twistedP F ζ hζ C s (f.val k), by
        rcases f.property with ⟨h, hh⟩
        refine ⟨borelPLevel F ζ hζ C s J h, ?_⟩
        funext k
        change (borelPLevel F ζ hζ C s J h).val.val k.val = _
        rw [borelPLevel_formula]
        exact congrArg (twistedP F ζ hζ C s) (congrFun hh k)⟩
      map_add' := by
        intro f h
        apply Subtype.ext
        funext k
        exact (twistedP F ζ hζ C s).map_add (f.val k) (h.val k)
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext k
        exact (twistedP F ζ hζ C s).map_smul c (f.val k) }
  refine ⟨m, ?_⟩
  change @Continuous _ _ (compactLevelTopology F ζ hζ _ J K)
    (compactLevelTopology F ζ hζ _ J K) m
  apply continuous_coinduced_dom.mpr
  have heq : (m ∘ restrictLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K) =
      (restrictLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K ∘
        borelPLevel F ζ hζ C s J) := by
    funext f
    apply Subtype.ext
    funext k
    exact (borelPLevel_formula F ζ hζ C s J f k.val).symm
  rw [heq]
  exact continuous_coinduced_rng.comp (borelPLevel_continuous F ζ hζ C s J)

def compactQ (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    CompactLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K →L[ℂ]
      CompactLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K := by
  let m : CompactLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K →ₗ[ℂ]
      CompactLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K :=
    { toFun := fun f => ⟨fun k => twistedQ F ζ hζ C s (f.val k), by
        rcases f.property with ⟨h, hh⟩
        refine ⟨borelQLevel F ζ hζ C s J h, ?_⟩
        funext k
        change (borelQLevel F ζ hζ C s J h).val.val k.val = _
        rw [borelQLevel_formula]
        exact congrArg (twistedQ F ζ hζ C s) (congrFun hh k)⟩
      map_add' := by
        intro f h
        apply Subtype.ext
        funext k
        exact (twistedQ F ζ hζ C s).map_add (f.val k) (h.val k)
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext k
        exact (twistedQ F ζ hζ C s).map_smul c (f.val k) }
  refine ⟨m, ?_⟩
  change @Continuous _ _ (compactLevelTopology F ζ hζ _ J K)
    (compactLevelTopology F ζ hζ _ J K) m
  apply continuous_coinduced_dom.mpr
  have heq : (m ∘ restrictLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K) =
      (restrictLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K ∘
        borelQLevel F ζ hζ C s J) := by
    funext f
    apply Subtype.ext
    funext k
    exact (borelQLevel_formula F ζ hζ C s J f k.val).symm
  rw [heq]
  exact continuous_coinduced_rng.comp (borelQLevel_continuous F ζ hζ C s J)

 theorem compactP_formula (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
    (f : CompactLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K) (k : K) :
    (compactP F ζ hζ C s J K f).val k = twistedP F ζ hζ C s (f.val k) := by rfl

 theorem compactQ_formula (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
    (f : CompactLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K) (k : K) :
    (compactQ F ζ hζ C s J K f).val k = twistedQ F ζ hζ C s (f.val k) := by rfl

 theorem compactP_restriction_square (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
    (f : InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J) :
    restrictLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K
        (borelPLevel F ζ hζ C s J f) =
      compactP F ζ hζ C s J K
        (restrictLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K f) := by
  apply Subtype.ext
  funext k
  change (borelPLevel F ζ hζ C s J f).val.val k.val = _
  simp only [compactP_formula]
  exact borelPLevel_formula F ζ hζ C s J f k.val

 theorem compactQ_restriction_square (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
    (f : InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J) :
    restrictLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K
        (borelQLevel F ζ hζ C s J f) =
      compactQ F ζ hζ C s J K
        (restrictLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K f) := by
  apply Subtype.ext
  funext k
  change (borelQLevel F ζ hζ C s J f).val.val k.val = _
  simp only [compactQ_formula]
  exact borelQLevel_formula F ζ hζ C s J f k.val

 theorem compactP_compactQ (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
    (f : CompactLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J K) :
    compactP F ζ hζ C s J K (compactQ F ζ hζ C s J K f) = f := by
  apply Subtype.ext
  funext k
  rw [compactP_formula, compactQ_formula, twistedP_twistedQ]

 theorem compactQ_compactP (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
    (f : CompactLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J K) :
    compactQ F ζ hζ C s J K (compactP F ζ hζ C s J K f) = f := by
  apply Subtype.ext
  funext k
  rw [compactQ_formula, compactP_formula, twistedQ_twistedP]

def transportedP (C : ModelData F ζ hζ) (s : ℂ) :
    Smooth F ζ hζ (productModel F ζ hζ C) →L[ℂ] Smooth F ζ hζ (rationalModel F ζ hζ) :=
  (normTwist F ζ hζ (rationalModel F ζ hζ) s).symm.toContinuousLinearMap.comp
    ((twistedP F ζ hζ C s).comp
      (normTwist F ζ hζ (productModel F ζ hζ C) s).toContinuousLinearMap)

def transportedQ (C : ModelData F ζ hζ) (s : ℂ) :
    Smooth F ζ hζ (rationalModel F ζ hζ) →L[ℂ] Smooth F ζ hζ (productModel F ζ hζ C) :=
  (normTwist F ζ hζ (productModel F ζ hζ C) s).symm.toContinuousLinearMap.comp
    ((twistedQ F ζ hζ C s).comp
      (normTwist F ζ hζ (rationalModel F ζ hζ) s).toContinuousLinearMap)

 theorem transportedP_eq (C : ModelData F ζ hζ) (s : ℂ) :
    transportedP F ζ hζ C s = KPGlobalTorusPeriodizationInverse.periodization F ζ hζ C := by
  ext f
  simp [transportedP, twistedP]

 theorem transportedQ_eq (C : ModelData F ζ hζ) (s : ℂ) :
    transportedQ F ζ hζ C s = KPGlobalTorusPeriodizationInverse.averaging F ζ hζ C := by
  ext f
  simp [transportedQ, twistedQ]

 theorem finite_stage_P_holomorphic (C : ModelData F ζ hζ)
    (U : Submodule ℂ (Smooth F ζ hζ (productModel F ζ hζ C)))
    (V : Submodule ℂ (Smooth F ζ hζ (rationalModel F ζ hζ)))
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (bU : Module.Basis ι ℂ U) (bV : Module.Basis κ ℂ V)
    (hUV : ∀ s u, u ∈ U → transportedP F ζ hζ C s u ∈ V) (i : κ) (j : ι) :
    Differentiable ℂ (fun s => bV.repr
      ⟨transportedP F ζ hζ C s (bU j).val, hUV s _ (bU j).property⟩ i) := by
  have hc : (fun s : ℂ => bV.repr
      ⟨transportedP F ζ hζ C s (bU j).val, hUV s _ (bU j).property⟩ i) =
      (fun _ : ℂ => bV.repr
      ⟨transportedP F ζ hζ C 0 (bU j).val, hUV 0 _ (bU j).property⟩ i) := by
    funext s
    congr 2
    apply Subtype.ext
    simp only [transportedP_eq]
  rw [hc]
  exact differentiable_const _

 theorem finite_stage_Q_holomorphic (C : ModelData F ζ hζ)
    (U : Submodule ℂ (Smooth F ζ hζ (rationalModel F ζ hζ)))
    (V : Submodule ℂ (Smooth F ζ hζ (productModel F ζ hζ C)))
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (bU : Module.Basis ι ℂ U) (bV : Module.Basis κ ℂ V)
    (hUV : ∀ s u, u ∈ U → transportedQ F ζ hζ C s u ∈ V) (i : κ) (j : ι) :
    Differentiable ℂ (fun s => bV.repr
      ⟨transportedQ F ζ hζ C s (bU j).val, hUV s _ (bU j).property⟩ i) := by
  have hc : (fun s : ℂ => bV.repr
      ⟨transportedQ F ζ hζ C s (bU j).val, hUV s _ (bU j).property⟩ i) =
      (fun _ : ℂ => bV.repr
      ⟨transportedQ F ζ hζ C 0 (bU j).val, hUV 0 _ (bU j).property⟩ i) := by
    funext s
    congr 2
    apply Subtype.ext
    simp only [transportedQ_eq]
  rw [hc]
  exact differentiable_const _

 theorem twist_pointwise_holomorphic (P : Polarization F ζ hζ)
    (f : Smooth F ζ hζ P) (t : E F ζ hζ) :
    Differentiable ℂ (fun s => (normTwist F ζ hζ P s f).val.val t) := by
  simp only [normTwist_formula]
  exact (normPower_entire F ζ hζ t).mul_const _

theorem iwasawaUpperUnits (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (h10 : A 1 0 = 0) : IsUnit (A 0 0) ∧ IsUnit (A 1 1) := by
  have h : IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) (KPGlobalTorusFunctionData.Adeles F))) := (Matrix.GeneralLinearGroup.det A).isUnit
  have hd : Matrix.det (A : Matrix (Fin 2) (Fin 2) (KPGlobalTorusFunctionData.Adeles F)) = A 0 0 * A 1 1 := by simp [Matrix.det_fin_two, h10]
  exact ⟨isUnit_of_mul_isUnit_left (hd ▸ h), isUnit_of_mul_isUnit_right (hd ▸ h)⟩
def iwasawaUpperRatio (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (h10 : A 1 0 = 0) : KPGlobalTorusFunctionData.Ideles F :=
  (iwasawaUpperUnits F A h10).1.unit * (iwasawaUpperUnits F A h10).2.unit⁻¹
theorem iwasawaUpperRatio_scalar (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hA : A 1 0 = 0) (hB : B 1 0 = 0)
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B) : iwasawaUpperRatio F A hA = iwasawaUpperRatio F B hB := by
  obtain ⟨C, hC, he⟩ := (QuotientGroup.mk'_eq_mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).mp he
  obtain ⟨c, rfl⟩ := hC
  have he00 := congrArg (fun M : KPAdelicCoverRestrictedProduct.AdelicGL2 F => M 0 0) he
  have he11 := congrArg (fun M : KPAdelicCoverRestrictedProduct.AdelicGL2 F => M 1 1) he
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at he00 he11
  have hu00 : (iwasawaUpperUnits F A hA).1.unit * c = (iwasawaUpperUnits F B hB).1.unit := by
    apply Units.ext
    simpa only [Units.val_mul, IsUnit.unit_spec] using he00
  have hu11 : (iwasawaUpperUnits F A hA).2.unit * c = (iwasawaUpperUnits F B hB).2.unit := by
    apply Units.ext
    simpa only [Units.val_mul, IsUnit.unit_spec] using he11
  unfold iwasawaUpperRatio
  rw [← hu00, ← hu11]
  group
theorem iwasawaUpperMul_zero (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (hA : A 1 0 = 0) (hB : B 1 0 = 0) : (A * B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB]
theorem iwasawaUpperRatio_mul (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (hA : A 1 0 = 0) (hB : B 1 0 = 0) : iwasawaUpperRatio F (A * B) (iwasawaUpperMul_zero F A B hA hB) = iwasawaUpperRatio F A hA * iwasawaUpperRatio F B hB := by
  have hu00 : (iwasawaUpperUnits F (A * B) (iwasawaUpperMul_zero F A B hA hB)).1.unit = (iwasawaUpperUnits F A hA).1.unit * (iwasawaUpperUnits F B hB).1.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hB]
  have hu11 : (iwasawaUpperUnits F (A * B) (iwasawaUpperMul_zero F A B hA hB)).2.unit = (iwasawaUpperUnits F A hA).2.unit * (iwasawaUpperUnits F B hB).2.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA]
  unfold iwasawaUpperRatio
  rw [hu00, hu11]
  simp only [mul_inv_rev]
  ac_rfl

private theorem upperRoot_zero (x : KPGlobalTorusFunctionData.Adeles F) :
    upperRoot F x 1 0 = 0 := by simp [upperRoot_entries]

private theorem upperRoot_ratio (x : KPGlobalTorusFunctionData.Adeles F) :
    iwasawaUpperRatio F (upperRoot F x) (upperRoot_zero F x) = 1 := by
  have h00 : (iwasawaUpperUnits F (upperRoot F x) (upperRoot_zero F x)).1.unit = 1 := by
    apply Units.ext
    simp [IsUnit.unit_spec, upperRoot_entries]
  have h11 : (iwasawaUpperUnits F (upperRoot F x) (upperRoot_zero F x)).2.unit = 1 := by
    apply Units.ext
    simp [IsUnit.unit_spec, upperRoot_entries]
  simp [iwasawaUpperRatio, h00, h11]

theorem iwasawaUpperRatio_torus (t : E F ζ hζ)
    (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val) :
    iwasawaUpperRatio F A h10 = KPGlobalTorusFunctionData.p F ζ hζ t := by
  apply Units.ext
  change _ = (KPGlobalTorusFunctionData.torusRatio F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩ : KPGlobalTorusFunctionData.Adeles F)
  rw [KPGlobalTorusFunctionData.ratio_formula F _ A hA h10 h01]
  rfl

theorem iwasawaUpperRatio_torus_root (t : E F ζ hζ)
    (x : KPGlobalTorusFunctionData.Adeles F)
    (B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (hB : B 1 0 = 0)
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x)) :
    iwasawaUpperRatio F B hB = KPGlobalTorusFunctionData.p F ζ hζ t := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  have hrep : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (A * upperRoot F x) = QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B := by
    rw [map_mul, hA, ← projected_root F ζ hζ x, ← map_mul, ← he]
  rw [← iwasawaUpperRatio_scalar F (A * upperRoot F x) B
    (iwasawaUpperMul_zero F A (upperRoot F x) h10 (upperRoot_zero F x)) hB hrep,
    iwasawaUpperRatio_mul F A (upperRoot F x) h10 (upperRoot_zero F x),
    upperRoot_ratio, mul_one]
  exact iwasawaUpperRatio_torus F ζ hζ t A h10 h01 hA

 theorem twist_zero (P : Polarization F ζ hζ) : twist F ζ hζ P 0 = P := by
  unfold twist
  congr 1
  ext h
  change (P.character h : ℂ) * normPower F ζ hζ 0 h.val = (P.character h : ℂ)
  simp [normPower]
private theorem inducedCastValue (P Q P' Q' : Polarization F ζ hζ)
    (hP : P = P') (hQ : Q = Q')
    (A : Induced F ζ hζ P →L[ℂ] Induced F ζ hζ Q)
    (f : Induced F ζ hζ P') (g : G F ζ hζ) (t : E F ζ hζ) :
    (((congrArg₂ (fun R S => Induced F ζ hζ R →L[ℂ] Induced F ζ hζ S) hP hQ).mp A f).val.val g).val.val t =
      ((A ((congrArg (fun R => Induced F ζ hζ R) hP).mpr f)).val.val g).val.val t := by
  cases hP
  cases hQ
  rfl
private theorem inducedCastFiber (P P' : Polarization F ζ hζ)
    (hP : P = P') (f : Induced F ζ hζ P') (g : G F ζ hζ) :
    ((congrArg (fun R => Induced F ζ hζ R) hP).mpr f).val.val g =
      (congrArg (fun R => Smooth F ζ hζ R) hP).mpr (f.val.val g) := by
  cases hP
  rfl
private theorem smoothCastValue (P P' : Polarization F ζ hζ)
    (hP : P = P') (f : Smooth F ζ hζ P') (t : E F ζ hζ) :
    ((congrArg (fun R => Smooth F ζ hζ R) hP).mpr f).val.val t = f.val.val t := by
  cases hP
  rfl
private theorem normTwistZero (P : Polarization F ζ hζ) (f : Smooth F ζ hζ P) :
    (congrArg (fun R => Smooth F ζ hζ R) (twist_zero F ζ hζ P)).mpr f = normTwist F ζ hζ P 0 f := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  rw [smoothCastValue F ζ hζ _ _ (twist_zero F ζ hζ P) f t, normTwist_formula]
  simp [normPower]

def originalBorelP (C : ModelData F ζ hζ) :
    Induced F ζ hζ (productModel F ζ hζ C) →L[ℂ] Induced F ζ hζ (rationalModel F ζ hζ) := by
  let T := fun (P Q : Polarization F ζ hζ) => Induced F ζ hζ P →L[ℂ] Induced F ζ hζ Q
  exact (congrArg₂ T (twist_zero F ζ hζ (productModel F ζ hζ C))
    (twist_zero F ζ hζ (rationalModel F ζ hζ))).mp (borelP F ζ hζ C 0)

def originalBorelQ (C : ModelData F ζ hζ) :
    Induced F ζ hζ (rationalModel F ζ hζ) →L[ℂ] Induced F ζ hζ (productModel F ζ hζ C) := by
  let T := fun (P Q : Polarization F ζ hζ) => Induced F ζ hζ P →L[ℂ] Induced F ζ hζ Q
  exact (congrArg₂ T (twist_zero F ζ hζ (rationalModel F ζ hζ))
    (twist_zero F ζ hζ (productModel F ζ hζ C))).mp (borelQ F ζ hζ C 0)

 theorem originalBorelP_formula (C : ModelData F ζ hζ)
    (f : Induced F ζ hζ (productModel F ζ hζ C)) (g : G F ζ hζ) :
    (originalBorelP F ζ hζ C f).val.val g =
      KPGlobalTorusPeriodizationInverse.periodization F ζ hζ C (f.val.val g) := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  unfold originalBorelP
  rw [inducedCastValue F ζ hζ _ _ _ _ (twist_zero F ζ hζ _) (twist_zero F ζ hζ _)]
  rw [borelP_fiberwise, inducedCastFiber F ζ hζ _ _ (twist_zero F ζ hζ _)]
  rw [normTwistZero, twistedP_transport, normTwist_formula]
  simp [normPower]

 theorem originalBorelQ_formula (C : ModelData F ζ hζ)
    (f : Induced F ζ hζ (rationalModel F ζ hζ)) (g : G F ζ hζ) :
    (originalBorelQ F ζ hζ C f).val.val g =
      KPGlobalTorusPeriodizationInverse.averaging F ζ hζ C (f.val.val g) := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  unfold originalBorelQ
  rw [inducedCastValue F ζ hζ _ _ _ _ (twist_zero F ζ hζ _) (twist_zero F ζ hζ _)]
  rw [borelQ_fiberwise, inducedCastFiber F ζ hζ _ _ (twist_zero F ζ hζ _)]
  rw [normTwistZero, twistedQ_transport, normTwist_formula]
  simp [normPower]

private theorem compactCastValue (P Q P' Q' : Polarization F ζ hζ)
    (hP : P = P') (hQ : Q = Q')
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
    (A : CompactLevel F ζ hζ P J K →L[ℂ] CompactLevel F ζ hζ Q J K)
    (f : CompactLevel F ζ hζ P' J K) (k : K) (t : E F ζ hζ) :
    (((congrArg₂ (fun R S => CompactLevel F ζ hζ R J K →L[ℂ]
      CompactLevel F ζ hζ S J K) hP hQ).mp A f).val k).val.val t =
      ((A ((congrArg (fun R => CompactLevel F ζ hζ R J K) hP).mpr f)).val k).val.val t := by
  cases hP
  cases hQ
  rfl

private theorem compactCastFiber (P P' : Polarization F ζ hζ)
    (hP : P = P') (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (K : Subgroup (G F ζ hζ)) (f : CompactLevel F ζ hζ P' J K) (k : K) :
    ((congrArg (fun R => CompactLevel F ζ hζ R J K) hP).mpr f).val k =
      (congrArg (fun R => Smooth F ζ hζ R) hP).mpr (f.val k) := by
  cases hP
  rfl

def originalCompactP (C : ModelData F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    CompactLevel F ζ hζ (productModel F ζ hζ C) J K →L[ℂ]
      CompactLevel F ζ hζ (rationalModel F ζ hζ) J K := by
  let T := fun (P Q : Polarization F ζ hζ) => CompactLevel F ζ hζ P J K →L[ℂ]
    CompactLevel F ζ hζ Q J K
  exact (congrArg₂ T (twist_zero F ζ hζ (productModel F ζ hζ C))
    (twist_zero F ζ hζ (rationalModel F ζ hζ))).mp (compactP F ζ hζ C 0 J K)

def originalCompactQ (C : ModelData F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    CompactLevel F ζ hζ (rationalModel F ζ hζ) J K →L[ℂ]
      CompactLevel F ζ hζ (productModel F ζ hζ C) J K := by
  let T := fun (P Q : Polarization F ζ hζ) => CompactLevel F ζ hζ P J K →L[ℂ]
    CompactLevel F ζ hζ Q J K
  exact (congrArg₂ T (twist_zero F ζ hζ (rationalModel F ζ hζ))
    (twist_zero F ζ hζ (productModel F ζ hζ C))).mp (compactQ F ζ hζ C 0 J K)

 theorem originalCompactP_formula (C : ModelData F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
    (f : CompactLevel F ζ hζ (productModel F ζ hζ C) J K) (k : K) :
    (originalCompactP F ζ hζ C J K f).val k =
      KPGlobalTorusPeriodizationInverse.periodization F ζ hζ C (f.val k) := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  unfold originalCompactP
  rw [compactCastValue F ζ hζ _ _ _ _ (twist_zero F ζ hζ _) (twist_zero F ζ hζ _)]
  rw [compactP_formula, compactCastFiber F ζ hζ _ _ (twist_zero F ζ hζ _)]
  rw [normTwistZero, twistedP_transport, normTwist_formula]
  simp [normPower]

 theorem originalCompactQ_formula (C : ModelData F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
    (f : CompactLevel F ζ hζ (rationalModel F ζ hζ) J K) (k : K) :
    (originalCompactQ F ζ hζ C J K f).val k =
      KPGlobalTorusPeriodizationInverse.averaging F ζ hζ C (f.val k) := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  unfold originalCompactQ
  rw [compactCastValue F ζ hζ _ _ _ _ (twist_zero F ζ hζ _) (twist_zero F ζ hζ _)]
  rw [compactQ_formula, compactCastFiber F ζ hζ _ _ (twist_zero F ζ hζ _)]
  rw [normTwistZero, twistedQ_transport, normTwist_formula]
  simp [normPower]

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility

end
