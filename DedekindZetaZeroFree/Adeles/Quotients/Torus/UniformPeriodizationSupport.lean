module

public import DedekindZetaZeroFree.Eisenstein.Induction.UniformConjugateTorusFiberLevels
public import DedekindZetaZeroFree.Metaplectic.Torus.TwistedFiberPeriodization

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance fiberSupportSmoothTopology (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

local instance fiberSupportLevelAddGroup (P : Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P U) :=
  @Submodule.addCommGroup ℂ (KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P)
    inferInstance inferInstance inferInstance _

local instance fiberSupportStageAddGroup (C : ModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C) (P : Polarization F ζ hζ) :
    AddCommGroup (KPGlobalTorusFiniteStages.Stage F ζ hζ C L P) :=
  @Submodule.addCommGroup ℂ (KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P)
    inferInstance inferInstance inferInstance _

theorem unitary_torus_level_finite (C : ModelData F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    Module.Finite ℂ (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C) U) := by
  obtain ⟨L, hL⟩ := KPGlobalTorusFiniteStages.smooth_level_in_stage F ζ hζ C U _ (Or.inr rfl)
  letI := KPGlobalTorusFiniteStages.stage_module_finite F ζ hζ C L _ (Or.inr rfl)
  exact Module.Finite.of_injective (Submodule.inclusion hL) (Submodule.inclusion_injective hL)

theorem untwist_fiber_mem_unitary_level (C : ModelData F ζ hζ) (s : ℂ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (v : Smooth F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
    (hv : v.val ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (twist F ζ hζ (productModel F ζ hζ C) s) U) :
    (KPGlobalTorusPeriodizationInverse.untwistProduct F ζ hζ C
      ((normTwist F ζ hζ (productModel F ζ hζ C) s).symm v)).val ∈
        KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
          (KPGlobalTorusFiniteStages.productModel F ζ hζ C) U := by
  let H := (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
    (KPGlobalTorusFunctionData.torus F ζ hζ).subtype
  have hc : IsCompact (H : Set (E F ζ hζ)) :=
    (actualTorus_isClosed F ζ hζ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (globalLevel_isCompact F ζ hζ U)
  let w := KPGlobalTorusPeriodizationInverse.untwistProduct F ζ hζ C
    ((normTwist F ζ hζ (productModel F ζ hζ C) s).symm v)
  constructor
  · have hle : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ
        (KPGlobalTorusFiniteStages.productModel F ζ hζ C) ≤
        KPGlobalTorusFunctionData.ArchSmooth
          (KPGlobalTorusFiniteStages.productModel F ζ hζ C).H
          (KPGlobalTorusFiniteStages.productModel F ζ hζ C).character.toMonoidHom
          (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
          (KPGlobalTorusFunctionData.torusArchDomain F) :=
      iSup_le fun _ => inf_le_left
    exact hle w.property
  · intro j
    apply Subtype.ext
    funext t
    change w.val.val (t * j.val) = w.val.val t
    dsimp only [w]
    rw [KPGlobalTorusPeriodizationInverse.untwistProduct_formula,
      KPGlobalTorusPeriodizationInverse.untwistProduct_formula,
      normTwist_inverse_formula, normTwist_inverse_formula]
    have hδ := delta_compact_subgroup F ζ hζ H hc j
    have hν : KPGlobalCenterRationalCharacter.nu F ζ hζ j.val = 1 := by
      simp [KPGlobalCenterRationalCharacter.nu, hδ]
    have hnp : normPower F ζ hζ (-s) (t * j.val) = normPower F ζ hζ (-s) t := by
      simp [normPower, map_mul, hδ]
    rw [hnp, map_mul, hν, mul_one]
    rw [KPGlobalTorusFunctionData.rightLevel_covariance _ _ _ ⟨v.val, hv.2⟩ t j.val j.property]

theorem twisted_torus_level_finite (C : ModelData F ζ hζ) (s : ℂ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    Module.Finite ℂ (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (twist F ζ hζ (productModel F ζ hζ C) s) U) := by
  let hle : KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (twist F ζ hζ (productModel F ζ hζ C) s) U ≤
      Smooth F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) := le_iSup _ U
  let incl := Submodule.inclusion hle
  let A := (KPGlobalTorusPeriodizationInverse.untwistProduct F ζ hζ C).toLinearMap.comp
    (((normTwist F ζ hζ (productModel F ζ hζ C) s).symm.toLinearMap).comp incl)
  have hA : ∀ v, (A v).val ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C) U := by
    intro v
    exact untwist_fiber_mem_unitary_level F ζ hζ C s U (incl v) v.property
  let B : KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (twist F ζ hζ (productModel F ζ hζ C) s) U →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
        (KPGlobalTorusFiniteStages.productModel F ζ hζ C) U :=
    { toFun := fun v => ⟨(A v).val, hA v⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        change (A (v + w)).val = (A v).val + (A w).val
        exact congrArg (fun x : KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ C => x.val)
          (A.map_add v w)
      map_smul' := by
        intro c v
        apply Subtype.ext
        change (A (c • v)).val = c • (A v).val
        exact congrArg (fun x : KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ C => x.val)
          (A.map_smul c v) }
  letI := unitary_torus_level_finite F ζ hζ C U
  apply Module.Finite.of_injective B
  intro v w h
  have he : A v = A w := by
    apply Subtype.ext
    exact congrArg (fun x : KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C) U => x.val) h
  exact (Submodule.inclusion_injective hle)
    ((normTwist F ζ hζ (productModel F ζ hζ C) s).symm.injective
      ((KPGlobalTorusPeriodizationInverse.untwistProduct F ζ hζ C).injective he))

theorem finite_support_at_twisted_level (C : ModelData F ζ hζ) (s : ℂ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    ∃ S : Finset (KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C),
      ∀ v : KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
          (twist F ζ hζ (productModel F ζ hζ C) s) U,
        ∀ a ∉ S, v.val.val ((TorusChartTransport.rationalRep F ζ hζ C).lift a).val = 0 := by
  let V := KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
    (twist F ζ hζ (productModel F ζ hζ C) s) U
  let hle : V ≤ Smooth F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) :=
    le_iSup (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (twist F ζ hζ (productModel F ζ hζ C) s)) U
  let incl := Submodule.inclusion hle
  letI := twisted_torus_level_finite F ζ hζ C s U
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := ℂ) (M := V)
  have hex (i : Fin n) :
      ∃ S : Finset (KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C),
        ∀ a ∉ S, (b i).val.val ((TorusChartTransport.rationalRep F ζ hζ C).lift a).val = 0 := by
    let w := (normTwist F ζ hζ (productModel F ζ hζ C) s).symm (incl (b i))
    obtain ⟨W, hW, S, hS⟩ := KPGlobalTorusPeriodizationInverse.periodization_locally_finite
      F ζ hζ C (TorusChartTransport.rationalRep F ζ hζ C) w 1
    refine ⟨S, ?_⟩
    intro a ha
    have h := hS 1 (mem_of_mem_nhds hW) a ha
    obtain ⟨y, hy⟩ := TorusChartTransport.rationalRep_rational F ζ hζ C a
    have hnp : normPower F ζ hζ (-s)
        ((TorusChartTransport.rationalRep F ζ hζ C).lift a).val = 1 := by
      rw [hy]
      simp [normPower, KPGlobalTorusPeriodizationInverse.rationalLift, delta_rational]
    change ((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
      ((TorusChartTransport.rationalRep F ζ hζ C).lift a))⁻¹ : ℂˣ) *
      w.val.val (((TorusChartTransport.rationalRep F ζ hζ C).lift a).val * 1) = 0 at h
    rw [mul_one, normTwist_inverse_formula, hnp, one_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero _)
  choose S hS using hex
  refine ⟨Finset.univ.biUnion S, ?_⟩
  intro v a ha
  let ev : V →ₗ[ℂ] ℂ :=
    (KPGlobalTorusFunctionData.evaluation
      (twist F ζ hζ (productModel F ζ hζ C) s).H
      (twist F ζ hζ (productModel F ζ hζ C) s).character.toMonoidHom
      ((TorusChartTransport.rationalRep F ζ hζ C).lift a).val).comp V.subtype
  have he : ev = 0 := (Submodule.linearMap_eq_zero_iff_of_span_eq_top ev hb).mpr (by
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact hS i a (fun hai => ha (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hai⟩)))
  exact congrArg (fun L : V →ₗ[ℂ] ℂ => L v) he

theorem exists_uniform_chart_support (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (g : G F ζ hζ) :
    ∃ S : Finset (KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C),
      ∀ (f : InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
        (z : GroupArch F), ∀ a ∉ S,
          TorusChartTransport.chartTerm F ζ hζ C s f.val g a z = 0 := by
  obtain ⟨U, hU⟩ := exists_uniform_chart_fiber_level F ζ hζ J g
  obtain ⟨S, hS⟩ := finite_support_at_twisted_level F ζ hζ C s U
  refine ⟨S, ?_⟩
  intro f z a ha
  exact hS ⟨(f.val.val (groupArchChart F ζ hζ z * g)).val, hU _ f z⟩ a ha

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel
