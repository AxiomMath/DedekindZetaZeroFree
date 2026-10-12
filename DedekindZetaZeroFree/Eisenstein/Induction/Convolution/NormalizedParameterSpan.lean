module

public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationFiniteLevelCovers
public import DedekindZetaZeroFree.RepresentationTheory.Induction.FiniteDimensionalIntertwiners
public import DedekindZetaZeroFree.Eisenstein.Induction.Convolution.UniformFiniteLevel
public import DedekindZetaZeroFree.Algebra.LinearAlgebra.FiniteEvaluationReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource
open KPLiteralRaw
open KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ActualSourceStage
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming half_ne_zero → half_ne_zero
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming half_one → half_one
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming half_mul → half_mul
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming cToBorel → cToBorel
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming actual_cover_of_torus_cosets → actual_cover_of_torus_cosets

open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.FiniteScalarEvaluation renaming finite_evaluation_reconstruction → finite_evaluation_reconstruction
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

 theorem target_subgroup_eq :
    (KPSpatialSmoothing.P0 F ζ hζ).H = R F ζ hζ := by
  unfold KPSpatialSmoothing.P0 KPMsRationalCompactCrossPairing.targetPolarization
  rw [KPMsRationalCompactCrossPairing.actual_weyl_fibre]
  rfl

 def sourceH : KPSpatialSmoothing.actualC F ζ hζ →* R F ζ hζ :=
  (MulEquiv.subgroupCongr (target_subgroup_eq F ζ hζ)).toMonoidHom.comp
    (KPSpatialSmoothing.actualHCoordinate F ζ hζ)

 def sourceChi : KPSpatialSmoothing.actualC F ζ hζ →* ℂ where
  toFun c := KPGlobalTorusFunctionData.deltaHalf F ζ hζ (sourceH F ζ hζ c).val *
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (sourceH F ζ hζ c) : ℂ)
  map_one' := by simp only [map_one, Subgroup.coe_one, half_one, Units.val_one, mul_one]
  map_mul' c d := by
    simp only [map_mul, Subgroup.coe_mul, half_mul, Units.val_mul]
    ring

 theorem sourceChi_hN (h : (KPSpatialSmoothing.P0 F ζ hζ).H)
    (x : KPAdeles F) (c : KPSpatialSmoothing.actualC F ζ hζ)
    (hc : c.val = h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) :
    sourceChi F ζ hζ c = KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
        ((MulEquiv.subgroupCongr (target_subgroup_eq F ζ hζ)) h) : ℂ) := by
  have hh : KPSpatialSmoothing.actualHCoordinate F ζ hζ c = h := by
    have he : cToBorel F ζ hζ c =
      ActualBorelRetraction.torusInBorel F ζ hζ h.val *
      ActualBorelRetraction.rootInBorel F ζ hζ (Multiplicative.ofAdd x) := Subtype.ext hc
    apply Subtype.ext
    change ActualBorelRetraction.retraction F ζ hζ _ = h.val
    rw [he, map_mul, ActualBorelRetraction.retraction_torus,
      ActualBorelRetraction.retraction_root, mul_one]
  change KPGlobalTorusFunctionData.deltaHalf F ζ hζ
      ((MulEquiv.subgroupCongr (target_subgroup_eq F ζ hζ))
        (KPSpatialSmoothing.actualHCoordinate F ζ hζ c)).val *
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
      ((MulEquiv.subgroupCongr (target_subgroup_eq F ζ hζ))
        (KPSpatialSmoothing.actualHCoordinate F ζ hζ c)) : ℂ) = _
  rw [hh]
  rfl

private theorem half_power (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    KPGlobalExceptionalParameter.realLogPower
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) (1 / 2) =
        KPGlobalTorusFunctionData.deltaHalf F ζ hζ t := by
  have hp : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
  unfold KPGlobalTorusFunctionData.deltaHalf KPGlobalExceptionalParameter.realLogPower
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

 theorem source_covariant (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (μ : Measure K)
    (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ) (h : C(K, ℂ))
    (c : KPSpatialSmoothing.actualC F ζ hζ) (g : G F ζ hζ) :
    source F ζ hζ K hK μ f a s h (c.val * g) =
      sourceChi F ζ hζ c * source F ζ hζ K hK μ f a s h g := by
  obtain ⟨r, x, hc⟩ := (KPSpatialSmoothing.mem_actualC_iff F ζ hζ c.val).mp c.property
  have hh := source_covariance F ζ hζ K hK μ f a s h
    ((MulEquiv.subgroupCongr (target_subgroup_eq F ζ hζ)) r) x g
  rw [half_power] at hh
  rw [sourceChi_hN F ζ hζ r x c hc, hc]
  exact hh

private theorem normalized_parameter_span_finite
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ) (h : C(K, ℂ))
    (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    Module.Finite ℂ (Submodule.span ℂ
      (Set.range (fun s : ℂ => source F ζ hζ K hK μ f a s h))) := by
  obtain ⟨W, hW, hhW, hi⟩ := representative_kernelFinite F ζ hζ K h hh
  let := hW
  obtain ⟨J, hJ⟩ := CommonLevel.source_uniform_level F ζ hζ K hK f a
  let D := KPLiteralChamber.literalIwasawa F ζ hζ K hK
  obtain ⟨J0, n, r, hle, hnorm, htorus⟩ :=
    KPSpatialSmoothing.actual_normalized_torus_finite_cover F ζ hζ D J
  have hcover := actual_cover_of_torus_cosets F ζ hζ D J0 n r hnorm htorus
  let C := KPSpatialSmoothing.actualC F ζ hζ
  let χ := sourceChi F ζ hζ
  let JG := KPGlobalTorusFunctionData.globalLevel F ζ hζ J0
  let τ := kernelOn F ζ hζ K W hi
  let ρ := CovariantSampling.rho_J C K JG χ hnorm
  let A := τ.IntertwiningMap ρ
  have hcov : ∀ g : G F ζ hζ, ∃ (i : Fin n) (c : C) (k : K) (j : JG),
      g = c.val * (r i).val * k.val * j.val := by
    intro g
    obtain ⟨i, u, x, k, j, hg⟩ := hcover g
    let c : C := ⟨u.val.val * KPGlobalTorusFunctionData.N F ζ hζ x,
      (KPSpatialSmoothing.mem_actualC_iff F ζ hζ _).mpr ⟨u, x, rfl⟩⟩
    exact ⟨i, c, k, j, hg⟩
  let : Module.Finite ℂ A := by
    change Module.Finite ℂ (τ.IntertwiningMap (CovariantSampling.rho_J C K JG χ hnorm))
    exact CovariantSampling.intertwiningMap_finiteDimensional
      (W := W) C K JG χ n (fun i => (r i).val) hcov hnorm τ
  let T : ℂ → A := fun s =>
    { toLinearMap :=
        { toFun := fun w => ⟨source F ζ hζ K hK μ f a s w.val, by
            exact ⟨source_covariant F ζ hζ K hK μ f a s w.val,
              fun j g => hJ μ s w.val g j.val (hle j.property)⟩⟩
          map_add' := by intro u v; exact Subtype.ext ((sourceMap F ζ hζ K hK μ f a s).map_add u.val v.val)
          map_smul' := by intro c u; exact Subtype.ext ((sourceMap F ζ hζ K hK μ f a s).map_smul c u.val) }
      isIntertwining' := by
        intro k
        ext w g
        exact congrFun (source_intertwines F ζ hζ K hK μ f a s w.val k) g }
  let ev : A →ₗ[ℂ] Functions F ζ hζ :=
    { toFun := fun t => (t ⟨h, hhW⟩).val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hsub : Submodule.span ℂ (Set.range (fun s : ℂ => source F ζ hζ K hK μ f a s h)) ≤ ev.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact ⟨T s, rfl⟩
  let : Module.Finite ℂ ev.range := Module.Finite.range ev
  exact Module.Finite.of_injective (Submodule.inclusion hsub)
    (Submodule.inclusion_injective hsub)

 theorem normalized_entire_finite_expansion
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ) (h : C(K, ℂ))
    (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    ∃ (n : ℕ) (v : Fin n → Functions F ζ hζ) (c : Fin n → ℂ → ℂ),
      (∀ j, v j ∈ Submodule.span ℂ
        (Set.range (fun s : ℂ => source F ζ hζ K hK μ f a s h))) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) Set.univ) ∧
      ∀ s, source F ζ hζ K hK μ f a s h = ∑ j, c j s • v j := by
  let V := Submodule.span ℂ (Set.range (fun s : ℂ => source F ζ hζ K hK μ f a s h))
  let : Module.Finite ℂ V := normalized_parameter_span_finite F ζ hζ K hK μ f a h hh
  obtain ⟨n, m, x, A, b, hb⟩ :=
    finite_evaluation_reconstruction V
  let c : Fin n → ℂ → ℂ := fun j s => ∑ i, A j i * source F ζ hζ K hK μ f a s h (x i)
  refine ⟨n, fun j => (b j).val, c, fun j => (b j).property, ?_, ?_⟩
  · intro j s _
    apply Finset.analyticAt_fun_sum
    intro i _
    have hs : AnalyticAt ℂ (fun s => source F ζ hζ K hK μ f a s h (x i)) s :=
      (normalized_source_entire F ζ hζ K hK μ f a h (x i)).analyticAt s
    exact analyticAt_const.mul hs
  · intro s
    funext g
    have hv : source F ζ hζ K hK μ f a s h ∈ V := Submodule.subset_span ⟨s, rfl⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, c] using hb ⟨_, hv⟩ g

end DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource

end
