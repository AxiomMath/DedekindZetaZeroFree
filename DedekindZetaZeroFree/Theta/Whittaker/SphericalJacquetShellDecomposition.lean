module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ThreeShellCoordinates
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ValuationShellGeometry
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ValuationShellIntegralPartition
public import DedekindZetaZeroFree.MeasureTheory.Bochner.StableIntegralLinearMap
public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedResidualFunctionals

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualJacquet
open scoped NumberField Valued ValuativeRel BigOperators Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPExteriorUnitShellIntegrals
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
variable (S : CanonicalFiniteInducingData F ζ hζ v)
variable (P : Polarization S.heisenberg)
variable (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]
abbrev VMinus := InducedModule P
abbrev IMinusActual := sectionSpace S.borel P .minus 0
def truncationBall (π : (valuation (LocalField F v)).integer) (R : ℕ) : Set (LocalField F v) :=
  {x | ∃ u : (valuation (LocalField F v)).integer,
    x = (π : LocalField F v) ^ (-(R : ℤ)) * (u : LocalField F v)}

variable [NormedAddCommGroup (VMinus F ζ hζ v S P)]

local instance fiberTopology : TopologicalSpace (VMinus F ζ hζ v S P) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _ (inferInstance : PseudoMetricSpace (VMinus F ζ hζ v S P)))

variable [NormedSpace ℂ (VMinus F ζ hζ v S P)]

def jacquetIntegrand (ψ : AddChar (LocalField F v) ℂ)
    (f : IMinusActual F ζ hζ v S P) (x : LocalField F v) :
    VMinus F ζ hζ v S P :=
  star (ψ x) • f.val (S.borel.liftedW *
    (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ v))

def truncatedIntegral (ψ : AddChar (LocalField F v) ℂ)
    (π : (valuation (LocalField F v)).integer) (R : ℕ) (f : IMinusActual F ζ hζ v S P) :
    VMinus F ζ hζ v S P :=
  ∫ x in truncationBall F v π R, jacquetIntegrand F ζ hζ v S P ψ f x ∂μ

theorem compact_integrability
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (f : IMinusActual F ζ hζ v S P) (R : ℕ) :
    IntegrableOn (jacquetIntegrand F ζ hζ v S P ψ f)
      (truncationBall F v π R) μ := by
  have hf : IsLocallyConstant f.val := by
    obtain ⟨J, hJ⟩ := f.property.2
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hc : Continuous (fun y : ActualCover F ζ hζ v => g⁻¹ * y) :=
      continuous_const.mul continuous_id
    have hmem : ∀ᶠ y in nhds g, g⁻¹ * y ∈ J :=
      hc.continuousAt.preimage_mem_nhds
        (by simpa using J.isOpen.mem_nhds J.one_mem)
    filter_upwards [hmem] with y hy
    have he := congrFun (hJ (g⁻¹ * y) hy) g
    simpa [vectorRightTranslation] using he
  have hopen : Continuous (fun x : LocalField F v =>
      S.borel.liftedW *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ v)) :=
    continuous_const.mul (continuous_subtype_val.comp
      (S.borel.upperRoot_continuous.comp continuous_ofAdd))
  have hphase : IsLocallyConstant (fun x : LocalField F v => star (ψ x)) := by
    apply IsLocallyConstant.comp (g := star)
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hc : Continuous (fun y : LocalField F v => y - x) :=
      continuous_id.sub continuous_const
    have hmem : ∀ᶠ y in nhds x,
        y - x ∈ (valuation (LocalField F v)).integer :=
      hc.continuousAt.preimage_mem_nhds
        (by simpa using ((Valuation.isOpen_integer (v := valuation (LocalField F v))).mem_nhds ((valuation (LocalField F v)).integer.zero_mem)))
    filter_upwards [hmem] with y hy
    have he := ψ.map_add_eq_mul (y - x) x
    rw [hcond.1 ⟨y - x, hy⟩] at he
    simpa using he
  have hint : Continuous (jacquetIntegrand F ζ hζ v S P ψ f) :=
    (hphase.comp₂ (hf.comp_continuous hopen) (fun c b => c • b)).continuous
  have hball : IsCompact (truncationBall F v π R) := by
    have hO : IsCompact ((valuation (LocalField F v)).integer : Set (LocalField F v)) :=
      IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F v) 1
    have himg := hO.image (f := fun x => (π : LocalField F v) ^ (-(R : ℤ)) * x)
      (continuous_const.mul continuous_id)
    convert himg using 1
    ext x
    simp only [truncationBall, Set.mem_image]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  exact hint.continuousOn.integrableOn_compact hball

end
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
variable (S : CanonicalFiniteInducingData F ζ hζ v)
variable (P : Polarization S.heisenberg)
variable (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]

theorem unipotent_difference_identity (f : IMinusActual F ζ hζ v S P)
    (t : LocalField F v) :
    (IMinus S.borel P
      (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v) f - f).val 1 = 0 := by
  change f.val (1 * (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v)) - f.val 1 = 0
  rw [one_mul, show (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v) =
    (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v) * 1 by simp,
    f.property.1, upperRoot_trivial, sub_self]

theorem unipotent_open_coordinate (f : IMinusActual F ζ hζ v S P)
    (t x : LocalField F v) :
    (IMinus S.borel P
      (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v) f).val
      (S.borel.liftedW *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ v)) =
    f.val (S.borel.liftedW *
      (S.borel.upperRoot (Multiplicative.ofAdd (x + t)) : ActualCover F ζ hζ v)) := by
  change f.val ((_ * _) * _) = _
  rw [mul_assoc, ← Subgroup.coe_mul, ← map_mul]
  rfl

private theorem kernel_compact (f : IMinusActual F ζ hζ v S P) (hf : f.val 1 = 0) :
    HasCompactSupport (fun x : LocalField F v => f.val (S.borel.liftedW *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ v))) := by
  classical
  let B := S.openCell P
  have hproj : S.borel.projection =
      KPLocalSmoothRepresentation.projection F ζ hζ v := by
    apply MonoidHom.ext
    intro g
    obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective
      (KPPGLLocalCover.splitScalarSubgroup F ζ hζ (Sum.inr v)) g
    rw [← hr]
    exact B.projection_eq r
  obtain ⟨J, hJ⟩ := f.property.2
  have hL := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ v
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ v)
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ v)).2.1
  have hn : {y : LocalField F v | KPLocalSmoothRepresentation.lowerRoot F ζ hζ v
      (Multiplicative.ofAdd y) ∈ J} ∈ nhds 0 := by
    apply hL.continuousAt.preimage_mem_nhds
    have hz : KPPGLLocalCover.LowerN F ζ hζ (Sum.inr v) 0 = 1 :=
      (KPLocalSmoothRepresentation.lowerRoot F ζ hζ v).map_one
    rw [hz]
    exact J.isOpen.mem_nhds J.one_mem
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hn
  have hzero : ∀ y : LocalField F v, ‖y‖ < ε →
      f.val (KPLocalSmoothRepresentation.lowerRoot F ζ hζ v (Multiplicative.ofAdd y)) = 0 := by
    intro y hy
    have hj := congrFun (hJ _ (he (by simpa [Metric.mem_ball, dist_zero_right] using hy))) 1
    simpa [vectorRightTranslation, hf] using hj
  have hlarge : ∀ x : LocalField F v, ε⁻¹ < ‖x‖ →
      f.val (S.borel.liftedW *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ v)) = 0 := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h; simp [h] at hx; linarith [inv_pos.mpr hε]
    have hxi : ‖x⁻¹‖ < ε := by
      rw [norm_inv]
      exact (inv_lt_comm₀ (norm_pos_iff.mpr hx0) hε).mpr hx
    let g := S.borel.liftedW *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ v)
    let A := KubotaRankTwo.w (LocalField F v) * KubotaRankTwo.n (LocalField F v) x
    have hA : Matrix.ProjGenLinGroup.mk A = KPLocalSmoothRepresentation.projection F ζ hζ v g := by
      rw [← hproj]
      change Matrix.ProjGenLinGroup.mk (_ * _) = _
      rw [map_mul, map_mul, S.borel.liftedW_projection,
        S.borel.upperRoot_projection]
      rfl
    have hd : g ∈ KPJacquetBruhatCharts.delta F ζ hζ v := by
      refine ⟨A, hA, ?_⟩
      simpa [A, KubotaRankTwo.coe_w, KubotaRankTwo.coe_n, Units.val_mul,
        Matrix.mul_apply, Fin.sum_univ_two] using hx0
    have hc : KPJacquetBruhatCharts.deltaCoordinate F ζ hζ v ⟨g, hd⟩ = x⁻¹ := by
      rw [KPJacquetBruhatCharts.deltaCoordinate_eq F ζ hζ v _ A hA]
      simp [A, KubotaRankTwo.coe_w, KubotaRankTwo.coe_n, Units.val_mul,
        Matrix.mul_apply, Fin.sum_univ_two, one_div]
    let b := (KPJacquetBruhatCharts.deltaInverse F ζ hζ v ⟨g, hd⟩).1
    have hb : b.val * KPLocalSmoothRepresentation.lowerRoot F ζ hζ v
        (Multiplicative.ofAdd (x⁻¹)) = g := by
      change (g * (KPLocalSmoothRepresentation.lowerRoot F ζ hζ v (Multiplicative.ofAdd
        (KPJacquetBruhatCharts.deltaCoordinate F ζ hζ v ⟨g, hd⟩)))⁻¹) * _ = g
      rw [hc, inv_mul_cancel_right]
    let b' : S.borel.B := ⟨b.val, by rw [S.borel_eq]; exact b.property⟩
    change f.val g = 0
    rw [← hb]
    change f.val ((b' : ActualCover F ζ hζ v) * _) = 0
    rw [f.property.1, hzero _ hxi, map_zero]
  apply HasCompactSupport.intro (K := Metric.closedBall 0 ε⁻¹)
  · exact isCompact_closedBall _ _
  · intro x hx
    apply hlarge x
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx

private theorem valuation_norm_le (x y : LocalField F v) :
    valuation (LocalField F v) x ≤ valuation (LocalField F v) y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← Valuation.Compatible.vle_iff_le]
  change Valued.v x ≤ Valued.v y ↔ _
  exact (Valued.toNormedField.norm_le_iff).symm

private theorem ball_norm (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (R : ℕ) (x : LocalField F v) :
    x ∈ truncationBall F v π R ↔ ‖x‖ ≤ ‖(π : LocalField F v)‖ ^ (-(R : ℤ)) := by
  have hp : (π : LocalField F v) ≠ 0 := by
    intro h; exact hπ.ne_zero (Subtype.ext h)
  have hm : ∀ y : LocalField F v, y ∈ (valuation (LocalField F v)).integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← map_one (valuation (LocalField F v)), valuation_norm_le]
    simp
  change (∃ u : (valuation (LocalField F v)).integer,
    x = (π : LocalField F v) ^ (-(R : ℤ)) * (u : LocalField F v)) ↔ _
  constructor
  · rintro ⟨u, rfl⟩
    rw [norm_mul, norm_zpow]
    exact mul_le_of_le_one_right (by positivity) ((hm _).mp u.property)
  · intro hx
    have hz : ‖(π : LocalField F v) ^ (-(R : ℤ))‖ ≠ 0 := norm_ne_zero_iff.mpr (zpow_ne_zero _ hp)
    refine ⟨⟨x / (π : LocalField F v) ^ (-(R : ℤ)), (hm _).mpr ?_⟩, ?_⟩
    · rw [norm_div, div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)), norm_zpow]
      exact hx
    · exact (mul_div_cancel₀ x (zpow_ne_zero _ hp)).symm

private theorem compact_cutoff (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    {E : Type*} [Zero E] (q : LocalField F v → E) (hq : HasCompactSupport q)
    (t : LocalField F v) :
    ∃ R₀ : ℕ, ∀ R ≥ R₀,
      t ∈ truncationBall F v π R ∧ ∀ x ∉ truncationBall F v π R, q x = 0 := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hq.isBounded
  have hp : ‖(π : LocalField F v)‖ < 1 := by
    have h := (Valuation.integer.integers (valuation (LocalField F v))).valuation_irreducible_lt_one hπ
    change valuation (LocalField F v) (π : LocalField F v) < 1 at h
    have hh : ¬ valuation (LocalField F v) 1 ≤ valuation (LocalField F v) (π : LocalField F v) := by
      simpa using (not_le.mpr h)
    rw [valuation_norm_le] at hh
    simpa using (not_le.mp hh)
  have hp0 : 0 < ‖(π : LocalField F v)‖ := norm_pos_iff.mpr (by
    intro h; exact hπ.ne_zero (Subtype.ext h))
  have ht := tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hp0 |>.mpr hp)
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop (max C ‖t‖)))
  refine ⟨R₀, fun R hR => ?_⟩
  have hbound : max C ‖t‖ ≤ ‖(π : LocalField F v)‖ ^ (-(R : ℤ)) := by
    simpa [zpow_neg, zpow_natCast, inv_pow] using hR₀ R hR
  refine ⟨(ball_norm F v π hπ R t).mpr ((le_max_right _ _).trans hbound), ?_⟩
  intro x hx
  by_contra hz
  apply hx
  apply (ball_norm F v π hπ R x).mpr
  exact (hC x (subset_closure hz)).trans ((le_max_left _ _).trans hbound)

private theorem ball_translate (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (R : ℕ) (t : LocalField F v) (ht : t ∈ truncationBall F v π R) (x : LocalField F v) :
    x + t ∈ truncationBall F v π R ↔ x ∈ truncationBall F v π R := by
  simp only [ball_norm F v π hπ] at *
  constructor
  · intro hx
    have h := IsUltrametricDist.norm_add_le_max (x + t) (-t)
    simpa using h.trans (max_le hx (by simpa using ht))
  · intro hx
    exact (IsUltrametricDist.norm_add_le_max x t).trans (max_le hx ht)

private theorem integral_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (R : ℕ) (t : LocalField F v) (ht : t ∈ truncationBall F v π R)
    (q : LocalField F v → E) :
    (∫ x in truncationBall F v π R, q (x + t) ∂μ) =
      ∫ x in truncationBall F v π R, q x ∂μ := by
  classical
  have hs : MeasurableSet (truncationBall F v π R) := by
    have he : truncationBall F v π R = Metric.closedBall 0 (‖(π : LocalField F v)‖ ^ (-(R : ℤ))) := by
      ext x; simp [ball_norm F v π hπ, Metric.mem_closedBall, dist_zero_right]
    rw [he]; exact Metric.isClosed_closedBall.measurableSet
  rw [← integral_indicator hs, ← integral_indicator hs]
  let q' := (truncationBall F v π R).indicator q
  calc
    _ = ∫ x, q' (x + t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [q', Set.indicator_apply]
      rw [ball_translate F v π hπ R t ht]
    _ = _ := integral_add_right_eq_self q' t

end
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
variable (S : CanonicalFiniteInducingData F ζ hζ v)
variable (P : Polarization S.heisenberg)
variable (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]
variable (N : AddGroupNorm (VMinus F ζ hζ v S P))
variable (hN : ∀ (c : ℂ) (b : VMinus F ζ hζ v S P), N (c • b) = ‖c‖ * N b)

theorem open_cell_stabilization_compatible
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (f : IMinusActual F ζ hζ v S P) :
    letI := CompatibleFiniteNorm.normedAddCommGroup N
    letI := CompatibleFiniteNorm.normedSpace N hN
    letI := CompatibleFiniteNorm.topology N
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      truncatedIntegral F ζ hζ v S P μ ψ π R f =
        truncatedIntegral F ζ hζ v S P μ ψ π R₀ f := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  obtain ⟨u, hu⟩ := hcond.2
  let t : LocalField F v := (π : LocalField F v)⁻¹ * u
  have ht : ψ t ≠ 1 := hu
  let f' := IMinus S.borel P
    (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v) f
  let d := f' - f
  have hd : d.val 1 = 0 := unipotent_difference_identity F ζ hζ v S P f t
  have hcompact := kernel_compact F ζ hζ v S P d hd
  obtain ⟨R₀, hR₀⟩ := compact_cutoff F v π hπ _ hcompact t
  have hphase (x : LocalField F v) : star (ψ x) = ψ t * star (ψ (x + t)) := by
    have h1 : ψ x = ψ (x + t) * ψ (-t) := by
      conv_lhs => rw [show x = (x + t) + (-t) by ring]
      rw [AddChar.map_add_eq_mul]
    have h2 : star (ψ (-t)) = ψ t := by
      rw [AddChar.map_neg_eq_inv, star_inv₀]
      have hconj : star (ψ t) = (ψ t)⁻¹ := by
        rw [Complex.star_def]
        exact (Complex.inv_eq_conj (hψunitary t)).symm
      rw [hconj, inv_inv]
    rw [h1, star_mul, h2, mul_comm]
  have htranslate (R : ℕ) (hR : R₀ ≤ R) :
      truncatedIntegral F ζ hζ v S P μ ψ π R f' =
      ψ t • truncatedIntegral F ζ hζ v S P μ ψ π R f := by
    unfold truncatedIntegral
    calc
      _ = ∫ x in truncationBall F v π R,
          ψ t • jacquetIntegrand F ζ hζ v S P ψ f (x + t) ∂μ := by
        apply setIntegral_congr_fun
        · have he : truncationBall F v π R =
              Metric.closedBall 0 (‖(π : LocalField F v)‖ ^ (-(R : ℤ))) := by
            ext x; simp [ball_norm F v π hπ, Metric.mem_closedBall, dist_zero_right]
          rw [he]; exact Metric.isClosed_closedBall.measurableSet
        · intro x hx
          change star (ψ x) • f'.val _ = ψ t • (star (ψ (x + t)) • f.val _)
          rw [show f'.val _ = f.val (S.borel.liftedW *
            (S.borel.upperRoot (Multiplicative.ofAdd (x + t)) : ActualCover F ζ hζ v)) from
            unipotent_open_coordinate F ζ hζ v S P f t x, hphase x, smul_smul]
      _ = _ := by
        rw [integral_smul, integral_translate F v μ π hπ R t (hR₀ R hR).1]
  have hdint (R : ℕ) :
      truncatedIntegral F ζ hζ v S P μ ψ π R d =
        truncatedIntegral F ζ hζ v S P μ ψ π R f' -
        truncatedIntegral F ζ hζ v S P μ ψ π R f := by
    unfold truncatedIntegral
    have he : jacquetIntegrand F ζ hζ v S P ψ d = fun x =>
        jacquetIntegrand F ζ hζ v S P ψ f' x - jacquetIntegrand F ζ hζ v S P ψ f x := by
      funext x
      change star (ψ x) • (f'.val _ - f.val _) = _
      rw [smul_sub]
      rfl
    rw [he]
    exact integral_sub
      (compact_integrability F ζ hζ v S P μ
        hgood π hπ ψ hψcont hψunitary hcond f' R)
      (compact_integrability F ζ hζ v S P μ
        hgood π hπ ψ hψcont hψunitary hcond f R)
  have hdstable (R : ℕ) (hR : R₀ ≤ R) :
      truncatedIntegral F ζ hζ v S P μ ψ π R d =
      truncatedIntegral F ζ hζ v S P μ ψ π R₀ d := by
    unfold truncatedIntegral
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
    · dsimp [jacquetIntegrand]
      rw [(hR₀ R₀ le_rfl).2 x hx, smul_zero]
    · dsimp [jacquetIntegrand]
      rw [(hR₀ R hR).2 x hx, smul_zero]
  have hfactor (b : VMinus F ζ hζ v S P) : ψ t • b - b = (ψ t - 1) • b := by
    rw [sub_smul, one_smul]
  refine ⟨R₀, fun R hR => ?_⟩
  have he := hdstable R hR
  rw [hdint, hdint, htranslate R hR, htranslate R₀ le_rfl, hfactor, hfactor] at he
  exact (smul_right_injective _ (sub_ne_zero.mpr ht)) he

def IsStableJacquet (ψ : AddChar (LocalField F v) ℂ)
    (π : (valuation (LocalField F v)).integer)
    (J : IMinusActual F ζ hζ v S P →ₗ[ℂ] VMinus F ζ hζ v S P) : Prop :=
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  ∀ f, ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    truncatedIntegral F ζ hζ v S P μ ψ π R f = J f

theorem exists_unique_stableJacquet
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π) :
    ∃! J : IMinusActual F ζ hζ v S P →ₗ[ℂ] VMinus F ζ hζ v S P,
      IsStableJacquet F ζ hζ v S P μ N hN ψ π J := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  let g : IMinusActual F ζ hζ v S P →ₗ[ℂ] (LocalField F v → VMinus F ζ hζ v S P) :=
    { toFun := jacquetIntegrand F ζ hζ v S P ψ
      map_add' := by
        intro f g
        funext x
        simp [jacquetIntegrand, smul_add]
      map_smul' := by
        intro c f
        funext x
        simp only [jacquetIntegrand, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  exact KPExteriorActualJacquetShells.linearMap_of_eventual_integrals
    μ (truncationBall F v π) g
    (fun m f => compact_integrability F ζ hζ v S P μ hgood π hπ ψ hψcont hψunitary hcond f m)
    (open_cell_stabilization_compatible F ζ hζ v S P μ N hN hgood π hπ ψ hψcont hψunitary hcond)
private theorem integrand_translate
    (ψ : AddChar (LocalField F v) ℂ) (hψunitary : ∀ x, ‖ψ x‖ = 1)
    (f : IMinusActual F ζ hζ v S P) (t x : LocalField F v) :
    jacquetIntegrand F ζ hζ v S P ψ
      (IMinus S.borel P
        (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v) f) x =
      ψ t • jacquetIntegrand F ζ hζ v S P ψ f (x + t) := by
  have hu : ψ t * star (ψ t) = 1 := by
    simpa [hψunitary, Complex.star_def] using Complex.mul_conj' (ψ t)
  have hn : (S.borel.upperRoot (Multiplicative.ofAdd (x + t)) : ActualCover F ζ hζ v) =
      S.borel.upperRoot (Multiplicative.ofAdd x) *
        S.borel.upperRoot (Multiplicative.ofAdd t) := by
    exact congrArg Subtype.val (S.borel.upperRoot.map_mul _ _)
  change star (ψ x) • f.val ((S.borel.liftedW *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ v)) *
      S.borel.upperRoot (Multiplicative.ofAdd t)) = _
  simp only [jacquetIntegrand, hn, ← mul_assoc, ψ.map_add_eq_mul, star_mul, smul_smul]
  rw [hu, one_mul]

theorem stableJacquet_unipotent
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψunitary : ∀ x, ‖ψ x‖ = 1)
    (J : IMinusActual F ζ hζ v S P →ₗ[ℂ] VMinus F ζ hζ v S P)
    (hJ : IsStableJacquet F ζ hζ v S P μ N hN ψ π J)
    (f : IMinusActual F ζ hζ v S P) (t : LocalField F v) :
    J (IMinus S.borel P
      (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v) f) =
      ψ t • J f := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  let ft := IMinus S.borel P
    (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v) f
  obtain ⟨Rf, hRf⟩ := hJ f
  obtain ⟨Rt, hRt⟩ := hJ ft
  obtain ⟨Rb, hRb⟩ := compact_cutoff F v π hπ
    (fun _ : LocalField F v => (0 : ℂ)) HasCompactSupport.zero t
  let R := max Rb (max Rf Rt)
  have hb : t ∈ truncationBall F v π R := (hRb R (le_max_left _ _)).1
  rw [← hRt R ((le_max_right _ _).trans (le_max_right _ _)),
    ← hRf R ((le_max_left _ _).trans (le_max_right _ _))]
  change truncatedIntegral F ζ hζ v S P μ ψ π R ft = _
  unfold truncatedIntegral
  calc
    _ = ∫ x in truncationBall F v π R,
        ψ t • jacquetIntegrand F ζ hζ v S P ψ f (x + t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact integrand_translate F ζ hζ v S P ψ hψunitary f t x
    _ = ψ t • ∫ x in truncationBall F v π R,
        jacquetIntegrand F ζ hζ v S P ψ f (x + t) ∂μ := integral_smul (ψ t) _
    _ = _ := by rw [integral_translate F v μ π hπ R t hb]

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualJacquet

open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
variable (inducingData : CanonicalFiniteInducingData F ζ hζ v) (P : Polarization inducingData.heisenberg)
abbrev Fiber := InducedModule P
abbrev Action := weylConjugate P inducingData.borel.weyl
abbrev Sections := sectionSpace inducingData.borel P .minus 0
abbrev Compact (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :=
  (actualGoodCompactSplit F ζ hζ v ht).range
abbrev IntegralTorus (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :=
  (Compact F ζ hζ v ht).comap (Subgroup.subtype (actualTorus F ζ hζ v))
abbrev TorusLine (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :=
  fixedSubmodule (Action F ζ hζ v inducingData P) (IntegralTorus F ζ hζ v ht)
abbrev SectionLine (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :=
  letI : AddCommGroup (Sections F ζ hζ v inducingData P) := Submodule.addCommGroup _
  fixedSubmodule (V := Sections F ζ hζ v inducingData P)
    (IMinus inducingData.borel P) (Compact F ζ hζ v ht)

def Lift (y : (LocalField F v)ˣ) : actualTorus F ζ hζ v :=
  ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr v) y, by
    refine ⟨KubotaRankTwo.d (LocalField F v) y 1, ?_, ?_, ?_⟩
    · rfl
    · simp [KubotaRankTwo.d]
    · simp [KubotaRankTwo.d]⟩
abbrev QPower (r : ℝ) : ℂ :=
  (Real.rpow (residueCardinality (LocalField F v) : ℝ) r : ℂ)

def Orbit (π : (LocalField F v)ˣ) (b : Fiber F ζ hζ v inducingData P) (j : ℤ) :
    Fiber F ζ hζ v inducingData P :=
  QPower F v (-(j : ℝ) / 6) • Action F ζ hζ v inducingData P (Lift F ζ hζ v (π ^ j)) b
end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
variable (inducingData : CanonicalFiniteInducingData F ζ hζ v) (P : Polarization inducingData.heisenberg)

 lemma split_action_compact
    (I : IwasawaData inducingData.borel)
    (b : inducingData.borel.B) (hb : (b : ActualCover F ζ hζ v) ∈ I.compact.toOpenSubgroup)
    (x : Fiber F ζ hζ v inducingData P) :
    inducingAction inducingData.borel P .minus 0 b x =
      Action F ζ hζ v inducingData P (inducingData.borel.retract b) x := by
  change (inducingScalar inducingData.borel 0 b •
    borelAction inducingData.borel P .minus b) x = _
  have hs : inducingScalar inducingData.borel 0 b = 1 := by
    simp [inducingScalar, deltaHalf, normPower, I.intersection_norm b hb]
  rw [hs, one_smul]
  rfl

 def splitConstantPicture
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (I : IwasawaData inducingData.borel)
    (hR : ∀ b : inducingData.borel.B,
      (b : ActualCover F ζ hζ v) ∈ I.compact.toOpenSubgroup →
        inducingData.borel.retract b ∈ IntegralTorus F ζ hζ v ht)
    (x : TorusLine F ζ hζ v inducingData P ht) : compactPicture inducingData.borel P I .minus :=
  ⟨fun _ => x.val, by
    constructor
    · intro b k k' he
      have hb : (b : ActualCover F ζ hζ v) ∈ I.compact.toOpenSubgroup := by
        have hb' : (b : ActualCover F ζ hζ v) = k'.val * k.val⁻¹ := by
          rw [he]; simp [mul_assoc]
        rw [hb']
        exact I.compact.toOpenSubgroup.mul_mem k'.property
          (I.compact.toOpenSubgroup.inv_mem k.property)
      rw [split_action_compact F ζ hζ v inducingData P I b hb]
      exact (x.property ⟨_, hR b hb⟩).symm
    · refine ⟨⊤, ?_⟩
      intro j hj
      rfl⟩

private lemma split_picture_constant
    (I : IwasawaData inducingData.borel)
    (φ : compactLevel inducingData.borel P I .minus I.compact)
    (k : I.compact.toOpenSubgroup) : φ.val.val k = φ.val.val 1 := by
  exact φ.property k 1 k (by simp)

private lemma split_picture_fixed
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (I : IwasawaData inducingData.borel)
    (hC : (I.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ v)) =
      Compact F ζ hζ v ht)
    (φ : compactLevel inducingData.borel P I .minus I.compact) :
    φ.val.val 1 ∈ TorusLine F ζ hζ v inducingData P ht := by
  intro j
  have hj : (inducingData.borel.torus j.val : ActualCover F ζ hζ v) ∈
      I.compact.toOpenSubgroup := by
    change (inducingData.borel.torus j.val : ActualCover F ζ hζ v) ∈
      (I.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ v))
    rw [hC, inducingData.torus_full]
    exact j.property
  let k : I.compact.toOpenSubgroup := ⟨_, hj⟩
  have hc := φ.val.property.1 (inducingData.borel.torus j.val) 1 k (by simp [k])
  rw [split_picture_constant F ζ hζ v inducingData P I φ k,
    split_action_compact F ζ hζ v inducingData P I _ hj,
    inducingData.borel.retract_torus] at hc
  exact hc.symm

theorem compact_evaluation_of_split_iwasawa
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (I : IwasawaData inducingData.borel)
    (hC : (I.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ v)) =
      Compact F ζ hζ v ht)
    (hR : ∀ b : inducingData.borel.B,
      (b : ActualCover F ζ hζ v) ∈ I.compact.toOpenSubgroup →
        inducingData.borel.retract b ∈ IntegralTorus F ζ hζ v ht) :
    ∃ E : SectionLine F ζ hζ v inducingData P ht ≃ₗ[ℂ] TorusLine F ζ hζ v inducingData P ht,
      ∀ f, (E f).val = f.val.val 1 := by
  letI : AddCommGroup (Sections F ζ hζ v inducingData P) := Submodule.addCommGroup _
  let ef : compactLevel inducingData.borel P I .minus I.compact ≃ₗ[ℂ]
      TorusLine F ζ hζ v inducingData P ht := {
    toFun := fun φ => ⟨φ.val.val 1, split_picture_fixed F ζ hζ v inducingData P ht I hC φ⟩
    invFun := fun x => ⟨splitConstantPicture F ζ hζ v inducingData P ht I hR x, by
      intro j k k' he; rfl⟩
    left_inv := by
      intro φ
      apply Subtype.ext
      apply Subtype.ext
      funext k
      exact (split_picture_constant F ζ hζ v inducingData P I φ k).symm
    right_inv := by intro x; rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  let es : compactLevel inducingData.borel P I .minus I.compact ≃ₗ[ℂ]
      SectionLine F ζ hζ v inducingData P ht := {
    toFun := fun φ => ⟨compactTrivialization inducingData.borel P I .minus 0 φ.val, by
      change _ ∈ fixedSubmodule (IMinus inducingData.borel P) (Compact F ζ hζ v ht)
      rw [← hC]
      exact (compact_level_identification inducingData.borel P I .minus
        I.compact le_rfl 0 φ.val).mp φ.property⟩
    invFun := fun f => ⟨(compactTrivialization inducingData.borel P I .minus 0).symm f.val,
      (compact_level_identification inducingData.borel P I .minus I.compact le_rfl 0 _).mpr
        (by simpa only [LinearEquiv.apply_symm_apply, hC] using f.property)⟩
    left_inv := by
      intro φ
      apply Subtype.ext
      exact (compactTrivialization inducingData.borel P I .minus 0).symm_apply_apply φ.val
    right_inv := by
      intro f
      apply Subtype.ext
      exact (compactTrivialization inducingData.borel P I .minus 0).apply_symm_apply f.val
    map_add' := by intros; apply Subtype.ext; simp
    map_smul' := by intros; apply Subtype.ext; simp }
  refine ⟨es.symm.trans ef, ?_⟩
  intro f
  change ((es.symm f).val.val 1) = f.val.val 1
  have he : ∀ φ, (es φ).val.val 1 = φ.val.val 1 := by
    intro φ
    change inducingAction inducingData.borel P .minus 0 (I.borelPart 1)
      (φ.val.val (I.compactPart 1)) = φ.val.val 1
    have hb : I.borelPart 1 = 1 := by simpa using I.borelPart_compact 1
    have hk : I.compactPart 1 = 1 := by simpa using I.compactPart_compact 1
    rw [hb, hk]
    simp
  have h := he (es.symm f)
  rw [es.apply_symm_apply] at h
  exact h.symm

 lemma split_range_topology
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :
    IsCompact (Compact F ζ hζ v ht : Set (ActualCover F ζ hζ v)) ∧
      IsOpen (Compact F ζ hζ v ht : Set (ActualCover F ζ hζ v)) := by
  have h := KPPGLLocalCover.compactSplitting_topology F ζ hζ v ht
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ v)
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ v)
  have he : Set.range (KPPGLLocalCover.compactSplitting F ζ hζ v ht) =
      (Compact F ζ hζ v ht : Set (ActualCover F ζ hζ v)) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      induction g using QuotientGroup.induction_on with | _ g => exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨QuotientGroup.mk g, rfl⟩
  rw [he] at h
  exact h.2

private lemma split_factor
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (g : ActualCover F ζ hζ v) :
    ∃ b : inducingData.borel.B, ∃ k : Compact F ζ hζ v ht,
      g = b.val * k.val := by
  letI : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr v)) :=
    @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr v))
      (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr v))
  obtain ⟨G, hG⟩ := QuotientGroup.mk_surjective
    (KPPGLLocalCover.projection F ζ hζ (Sum.inr v) g)
  obtain ⟨r, hr⟩ := ActualFiniteBorel.IwasawaProof.triangularize F v G
  let k := actualGoodCompactSplit F ζ hζ v ht r⁻¹
  have hk : KPPGLLocalCover.projection F ζ hζ (Sum.inr v) k =
      KPPGLLocalCover.baseQuotient F (Sum.inr v) (KPTameCompact.inclusion F v r⁻¹) := rfl
  have hb : g * k⁻¹ ∈ inducingData.borel.B := by
    rw [inducingData.borel_eq]
    change KPLocalSmoothRepresentation.projection F ζ hζ v (g * k⁻¹) ∈
      KPRankOneInduction.upperBorel F v
    refine ⟨G * KPTameCompact.inclusion F v r, ?_, hr⟩
    change Matrix.ProjGenLinGroup.mk (G * KPTameCompact.inclusion F v r) =
      KPLocalSmoothRepresentation.ordinaryPGLMap F v
        (KPPGLLocalCover.projection F ζ hζ (Sum.inr v) (g * k⁻¹))
    rw [(KPPGLLocalCover.projection F ζ hζ (Sum.inr v)).map_mul,
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr v)).map_inv, ← hG, hk,
      map_inv, map_inv, inv_inv]
    rfl
  exact ⟨⟨g * k⁻¹, hb⟩, ⟨k, ⟨r⁻¹, rfl⟩⟩, by simp⟩

include P in
private lemma split_retract
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (b : inducingData.borel.B) (hb : b.val ∈ Compact F ζ hζ v ht) :
    inducingData.borel.retract b ∈ IntegralTorus F ζ hζ v ht := by
  obtain ⟨k, hk⟩ := hb
  have hbB : b.val ∈ actualBorel F ζ hζ v := inducingData.borel_eq ▸ b.property
  obtain ⟨A, hA, hA10⟩ := hbB
  have hp : Matrix.ProjGenLinGroup.mk (KPTameCompact.inclusion F v k) =
      KPLocalSmoothRepresentation.projection F ζ hζ v b.val := by
    rw [← hk]; rfl
  obtain ⟨u, he⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (hp.trans hA.symm)
  have hz : (KPTameCompact.inclusion F v k) 1 0 = 0 := by
    have he10 := congrArg (fun C : KPRankOneInduction.GL2 F v => C 1 0) he
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Fin.reduceEq, if_true, if_false, mul_zero, zero_add, add_zero, hA10] at he10
    exact (mul_eq_zero.mp he10).resolve_right u.ne_zero
  have hki : k 1 0 = 0 := by
    apply Subtype.ext
    simpa [KPTameCompact.inclusion, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply] using hz
  have hdet : IsUnit (k 0 0 * k 1 1) := by
    simpa [Matrix.det_fin_two, hki] using k.det.isUnit
  let a : (KPTameCompact.O F v)ˣ := (isUnit_of_mul_isUnit_left hdet).unit
  have ha : (a : KPTameCompact.O F v) = k 0 0 := (isUnit_of_mul_isUnit_left hdet).unit_spec
  let t : KPTameCompact.O F v := - (a⁻¹ : (KPTameCompact.O F v)ˣ) * k 0 1
  let d := k * KPStandardLocalRootLifts.integralN F v t
  have hd10 : (KPTameCompact.inclusion F v d) 1 0 = 0 := by
    simp [d, map_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, KPStandardLocalRootLifts.integralN, KPTameCompact.inclusion,
      KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply, hki]
  have hd01 : (KPTameCompact.inclusion F v d) 0 1 = 0 := by
    have hai : k 0 0 * ((a⁻¹ : (KPTameCompact.O F v)ˣ) : KPTameCompact.O F v) = 1 := by
      rw [← ha]; exact Units.mul_inv a
    have hdt : k 0 0 * t + k 0 1 = 0 := by
      dsimp [t]
      rw [← mul_assoc, mul_neg, hai]
      simp
    change ((KPTameCompact.O F v).subtype ((d 0 1))) = 0
    rw [show d 0 1 = 0 by
      simpa [d, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        KPStandardLocalRootLifts.integralN] using hdt]
    rfl
  let D := actualGoodCompactSplit F ζ hζ v ht d
  have hD : D ∈ actualTorus F ζ hζ v := by
    exact ⟨KPTameCompact.inclusion F v d, rfl, hd10, hd01⟩
  let j : actualTorus F ζ hζ v := ⟨D, hD⟩
  have hn : (inducingData.borel.upperRoot (Multiplicative.ofAdd (t : LocalField F v)) :
      ActualCover F ζ hζ v) = actualGoodCompactSplit F ζ hζ v ht
        (KPStandardLocalRootLifts.integralN F v t) := by
    rw [(inducingData.openCell P).upper_eq]
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v)
      (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr v) (t : LocalField F v)) = _
    rw [KPStandardLocalRootLifts.N_eq_compact F ζ hζ v ht t]
    rfl
  have hbj : b * inducingData.borel.upperRoot (Multiplicative.ofAdd (t : LocalField F v)) =
      inducingData.borel.torus j := by
    apply Subtype.ext
    rw [inducingData.torus_full]
    change b.val * _ = D
    rw [hn, ← hk]
    exact (actualGoodCompactSplit F ζ hζ v ht).map_mul _ _ |>.symm
  have hr : inducingData.borel.retract b = j := by
    have h := congrArg inducingData.borel.retract hbj
    simpa only [map_mul, inducingData.borel.retract_upperRoot, mul_one,
      inducingData.borel.retract_torus] using h
  change (inducingData.borel.retract b : ActualCover F ζ hζ v) ∈ Compact F ζ hζ v ht
  rw [hr]
  exact ⟨d, rfl⟩

include P in
private lemma split_projection (g : ActualCover F ζ hζ v) :
    inducingData.borel.projection g = KPLocalSmoothRepresentation.projection F ζ hζ v g := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
  exact (inducingData.openCell P).projection_eq r

include P in
private lemma split_ratio (b : inducingData.borel.B) :
    inducingData.borel.coordinate (inducingData.borel.retract b) =
      KPRankOneInduction.borelRatio F v
        ⟨KPLocalSmoothRepresentation.projection F ζ hζ v b.val,
          show b.val ∈ actualBorel F ζ hζ v from inducingData.borel_eq ▸ b.property⟩ := by
  obtain ⟨x, hx⟩ := inducingData.borel.borel_decomposition b
  let y := inducingData.borel.coordinate (inducingData.borel.retract b)
  let G := KubotaRankTwo.d (LocalField F v) y 1 *
    KubotaRankTwo.n (LocalField F v) (Multiplicative.toAdd x)
  have hG : Matrix.ProjGenLinGroup.mk G =
      KPLocalSmoothRepresentation.projection F ζ hζ v b.val := by
    rw [← split_projection F ζ hζ v inducingData P]
    have hp := congrArg (fun c : inducingData.borel.B => inducingData.borel.projection c.val) hx
    simpa only [G, y, Subgroup.coe_mul, map_mul, inducingData.borel.torus_projection,
      inducingData.borel.upperRoot_projection] using hp.symm
  have h10 : G 1 0 = 0 := by
    simp [G, KubotaRankTwo.d, KubotaRankTwo.n, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  apply Units.ext
  symm
  rw [KPRankOneInduction.borelRatio_eq F v _ G hG h10]
  simp [G, KubotaRankTwo.d, KubotaRankTwo.n, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, y]

include P in
private lemma split_intersection_norm
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (b : inducingData.borel.B) (hb : b.val ∈ Compact F ζ hζ v ht) :
    localAbs (LocalField F v) (inducingData.borel.coordinate (inducingData.borel.retract b)) = 1 := by
  rw [split_ratio F ζ hζ v inducingData P]
  have hbb : b.val ∈ actualBorel F ζ hζ v := inducingData.borel_eq ▸ b.property
  have hc : b.val ∈ KPRankOneCartanGeometry.coveredK0 F ζ hζ v := by
    obtain ⟨k, hk⟩ := hb
    exact ⟨k, hk ▸ rfl⟩
  exact ActualFiniteBorel.IwasawaProof.covered_intersection F ζ hζ v ⟨b.val, hbb⟩ hc

 def goodLevel
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :
    CompactOpenLevel (ActualCover F ζ hζ v) where
  toOpenSubgroup := {
    toSubgroup := Compact F ζ hζ v ht
    isOpen' := (split_range_topology F ζ hζ v ht).2 }
  isCompact := (split_range_topology F ζ hζ v ht).1

include P in
private lemma split_iwasawa
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :
    ∃ I : IwasawaData inducingData.borel,
      (I.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ v)) = Compact F ζ hζ v ht := by
  classical
  let L := goodLevel F ζ hζ v ht
  have hex (g : ActualCover F ζ hζ v) :
      ∃ b : inducingData.borel.B, ∃ k : L.toOpenSubgroup, g = b.val * k.val :=
    split_factor F ζ hζ v inducingData ht g
  let bp (g : ActualCover F ζ hζ v) : inducingData.borel.B :=
    if hg : g ∈ L.toOpenSubgroup then 1 else Classical.choose (hex g)
  let kp (g : ActualCover F ζ hζ v) : L.toOpenSubgroup :=
    if hg : g ∈ L.toOpenSubgroup then ⟨g, hg⟩
    else Classical.choose (Classical.choose_spec (hex g))
  refine ⟨{
    compact := L
    borelPart := bp
    compactPart := kp
    decomposition := ?_
    borelPart_compact := ?_
    compactPart_compact := ?_
    intersection_norm := ?_ }, rfl⟩
  · intro g
    by_cases hg : g ∈ L.toOpenSubgroup
    · simp [bp, kp, hg]
    · simpa [bp, kp, hg] using
        Classical.choose_spec (Classical.choose_spec (hex g))
  · intro k
    simp [bp, k.property]
  · intro k
    simp [kp, k.property]
  · intro b hb
    exact split_intersection_norm F ζ hζ v inducingData P ht b hb

theorem compact_evaluation_equiv
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :
    ∃ E : SectionLine F ζ hζ v inducingData P ht ≃ₗ[ℂ] TorusLine F ζ hζ v inducingData P ht,
      ∀ f, (E f).val = f.val.val 1 := by
  obtain ⟨I, hC⟩ := split_iwasawa F ζ hζ v inducingData P ht
  apply compact_evaluation_of_split_iwasawa F ζ hζ v inducingData P ht I hC
  intro b hb
  apply split_retract F ζ hζ v inducingData P ht b
  change b.val ∈ (I.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ v)) at hb
  rwa [hC] at hb
end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
variable (inducingData : CanonicalFiniteInducingData F ζ hζ v) (P : Polarization inducingData.heisenberg)

theorem normalized_orbit_period
    (π : (LocalField F v)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (π : LocalField F v)) = WithZero.exp (-1 : ℤ))
    (b : Fiber F ζ hζ v inducingData P) (j : ℤ) :
    Orbit F ζ hζ v inducingData P π b (j + 3) = Orbit F ζ hζ v inducingData P π b j := by
  have hlift : Lift F ζ hζ v (π ^ (j + 3)) =
      Lift F ζ hζ v (π ^ j) *
        (inducingData.borel.cubeLift π : actualTorus F ζ hζ v) := by
    apply Subtype.ext
    change KPPGLLocalCover.A F ζ hζ (Sum.inr v) (π ^ (j + 3)) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr v) (π ^ j) *
        ((inducingData.borel.cubeLift π : actualTorus F ζ hζ v) : ActualCover F ζ hζ v)
    rw [inducingData.cube_actual, KPPGLLocalCover.A_mul,
      (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.1 (π ^ j) π |>.2,
      one_pow, map_one, one_mul, zpow_add]
    rfl
  have hcentral (b' : Fiber F ζ hζ v inducingData P) :
      Action F ζ hζ v inducingData P (inducingData.borel.cubeLift π : actualTorus F ζ hζ v) b' =
        QPower F v (1 / 2) • b' := by
    change tau P (inducingData.borel.weyl
      (inducingData.borel.cubeLift π : actualTorus F ζ hζ v)) b' = _
    rw [← inducingData.borel.weylCenter_coe]
    rw [tau_hasCentralCharacter inducingData.heisenberg P]
    change (inducingData.heisenberg.ω
      (inducingData.borel.weylCenter (inducingData.borel.cubeLift π)) : ℂ) • b' = _
    rw [(KPLocalPrincipalSeries.uniformizer_weights inducingData.borel π hπ).2.2]
    rfl
  have hq : 0 < (KPLocalPrincipalSeries.residueCardinality (LocalField F v) : ℝ) := by
    unfold KPLocalPrincipalSeries.residueCardinality
    exact_mod_cast Nat.card_pos
  unfold Orbit
  rw [hlift, map_mul]
  change QPower F v (-((j + 3 : ℤ) : ℝ) / 6) •
      (Action F ζ hζ v inducingData P (Lift F ζ hζ v (π ^ j)))
        (Action F ζ hζ v inducingData P (inducingData.borel.cubeLift π : actualTorus F ζ hζ v) b) = _
  rw [hcentral, map_smul, smul_smul]
  congr 1
  unfold QPower
  rw [← Complex.ofReal_mul]
  apply congrArg (fun x : ℝ => (x : ℂ))
  change (KPLocalPrincipalSeries.residueCardinality (LocalField F v) : ℝ) ^
      (-((j + 3 : ℤ) : ℝ) / 6 : ℝ) *
    (KPLocalPrincipalSeries.residueCardinality (LocalField F v) : ℝ) ^ (1 / 2 : ℝ) = _
  rw [← Real.rpow_add hq]
  congr 1
  push_cast
  ring
end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
variable (inducingData : CanonicalFiniteInducingData F ζ hζ v) (P : Polarization inducingData.heisenberg)

private lemma unit_lift_compact
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (u : (KPTameCompact.O F v)ˣ) :
    Lift F ζ hζ v (KPTameCompact.unitInclusion F v u) ∈ IntegralTorus F ζ hζ v ht := by
  let g : KPTameCompact.K0 F v := ⟨Matrix.diagonal ![(u : KPTameCompact.O F v), 1],
    Matrix.diagonal ![((u⁻¹ : (KPTameCompact.O F v)ˣ) : KPTameCompact.O F v), 1],
    by simp [Matrix.diagonal_mul_diagonal]; ext i; fin_cases i <;> simp,
    by simp [Matrix.diagonal_mul_diagonal]; ext i; fin_cases i <;> simp⟩
  have hg : (g.val : Matrix (Fin 2) (Fin 2) (KPTameCompact.O F v)) =
      !![(u : KPTameCompact.O F v), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  change (Lift F ζ hζ v (KPTameCompact.unitInclusion F v u) : ActualCover F ζ hζ v) ∈
    (actualGoodCompactSplit F ζ hζ v ht).range
  refine ⟨g, ?_⟩
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v)
    (KPGoodCompactSplitting.kStar F ζ hζ v ht g) = _
  rw [KPGoodCompactSplitting.kStar_unit_diagonal F ζ hζ v ht u 1 g (by simpa using hg)]
  congr 1
  apply congrArg (KPLocalCover.sectionMap F ζ hζ (Sum.inr v))
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma dimension_three
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :
    Module.finrank ℂ (Fiber F ζ hζ v inducingData P) = 3 := by
  have h3 : (3 : (valuation (LocalField F v)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (LocalField F v)).integer := by
    change (3 : KPTameCompact.O F v) ∉ KPTameCompact.p F v
    intro h
    have hzero : (3 : KPTameCompact.O F v ⧸ KPTameCompact.p F v) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h
    letI : Nontrivial (KPTameCompact.O F v ⧸ KPTameCompact.p F v) :=
      Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal (KPTameCompact.O F v)).ne_top
    exact ht (CharP.ringChar_of_prime_eq_zero Nat.prime_three hzero)
  rw [(finite_heisenberg_induction inducingData.heisenberg P).2.2.2.2.2]
  rw [Nat.card_congr inducingData.cubeClassEquiv.toEquiv]
  rw [KPLocalTorus.card_cubeClasses_tame (LocalField F v) (algebraMap F (LocalField F v) (ζ ^ 4))
    ((hζ.pow (by norm_num) (by norm_num : 12 = 4 * 3)).map_of_injective
      (FaithfulSMul.algebraMap_injective F (LocalField F v))) h3]
  norm_num

private lemma unit_of_exp_zero (y : (LocalField F v)ˣ)
    (h : KPCubicExpansion.valuationExponent (LocalField F v) y = 0) :
    ∃ u : (KPTameCompact.O F v)ˣ, KPTameCompact.unitInclusion F v u = y := by
  have hn : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (y : LocalField F v)) ≠ 0 := by
    simpa using (Units.ne_zero y)
  have hv : valuation (LocalField F v) (y : LocalField F v) = 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)).injective
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (y : LocalField F v)) =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v) 1
    rw [map_one, ← WithZero.exp_log hn]
    have hl : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
        (valuation (LocalField F v) (y : LocalField F v))) = 0 := neg_eq_zero.mp h
    rw [hl, WithZero.exp_zero]
  let a : (valuation (LocalField F v)).integer := ⟨(y : LocalField F v), hv.le⟩
  have ha : IsUnit a := (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation (LocalField F v)))).mpr hv
  obtain ⟨u, hu⟩ := ha
  refine ⟨u, ?_⟩
  apply Units.ext
  exact congrArg (fun x : (valuation (LocalField F v)).integer => (x : LocalField F v)) hu

private lemma class_decomposition
    (π : (LocalField F v)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (π : LocalField F v)) = WithZero.exp (-1 : ℤ))
    (y : (LocalField F v)ˣ) :
    ∃ (j : Fin 3) (u : (KPTameCompact.O F v)ˣ),
      QuotientGroup.mk' (CubicCharacters.cubes (LocalField F v)ˣ) y =
        QuotientGroup.mk' (CubicCharacters.cubes (LocalField F v)ˣ)
          (π ^ (j.val : ℤ) * KPTameCompact.unitInclusion F v u) := by
  let n := KPCubicExpansion.valuationExponent (LocalField F v) y
  have hp : KPCubicExpansion.valuationExponent (LocalField F v) π = 1 := by
    simp [KPCubicExpansion.valuationExponent, hπ]
  have hz : KPCubicExpansion.valuationExponent (LocalField F v) (y / π ^ n) = 0 := by
    rw [div_eq_mul_inv, ← zpow_neg_one (π ^ n), KPCubicExpansion.valuationExponent_mul,
      KPCubicExpansion.valuationExponent_zpow, KPCubicExpansion.valuationExponent_zpow, hp]
    simp [n]
  obtain ⟨u, hu⟩ := unit_of_exp_zero F v (y / π ^ n) hz
  let j : Fin 3 := ⟨(n % 3).toNat, by omega⟩
  have hj : (j.val : ℤ) = n % 3 := by
    change ((n % 3).toNat : ℤ) = n % 3
    exact Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num : (3 : ℤ) ≠ 0))
  have hn : n = (j.val : ℤ) + 3 * (n / 3) := by rw [hj]; omega
  have hy : y = (π ^ (j.val : ℤ) * KPTameCompact.unitInclusion F v u) * (π ^ (n / 3)) ^ 3 := by
    rw [hu, ← zpow_natCast _ (3 : ℕ), ← zpow_mul]
    norm_num only at *
    calc
      y = (π ^ n) * (y / π ^ n) := by simp [div_eq_mul_inv, mul_comm, mul_left_comm]
      _ = _ := by
        conv_lhs => arg 1; rw [hn, zpow_add]
        rw [mul_comm (n / 3) (3 : ℤ)]
        simp only [mul_comm, mul_left_comm, mul_assoc]
  refine ⟨j, u, ?_⟩
  rw [hy, map_mul]
  have hc : QuotientGroup.mk' (CubicCharacters.cubes (LocalField F v)ˣ) ((π ^ (n / 3)) ^ 3) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨π ^ (n / 3), rfl⟩
  rw [hc, mul_one]

private lemma orbit_span_top {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (hirr : ρ.IsIrreducible) (b : V) (hb : b ≠ 0) :
    Submodule.span ℂ (Set.range (fun g : H => ρ g b)) = ⊤ := by
  let S : Subrepresentation ρ := ⟨Submodule.span ℂ (Set.range (fun g : H => ρ g b)), by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * a, by simp⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih⟩
  letI : ρ.IsIrreducible := hirr
  rcases eq_bot_or_eq_top S with h | h
  · have hmem : b ∈ S.toSubmodule := by
      exact Submodule.subset_span ⟨1, by simp⟩
    rw [h] at hmem
    exact (hb hmem).elim
  · exact congrArg Subrepresentation.toSubmodule h

private lemma normalized_span
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (π : (LocalField F v)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (π : LocalField F v)) = WithZero.exp (-1 : ℤ))
    (b : Fiber F ζ hζ v inducingData P) (hb : b ∈ TorusLine F ζ hζ v inducingData P ht) (hne : b ≠ 0) :
    Submodule.span ℂ (Set.range (fun i : Fin 3 => Orbit F ζ hζ v inducingData P π b (i.val : ℤ))) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun i : Fin 3 => Orbit F ζ hζ v inducingData P π b (i.val : ℤ)))
  have hprops := weyl_conjugate_properties inducingData.heisenberg P
    inducingData.borel.weyl inducingData.borel.weylCenter inducingData.borel.weylCenter_coe
  have htop := orbit_span_top (Action F ζ hζ v inducingData P) hprops.2.2.1 b hne
  apply top_unique
  rw [← htop]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  obtain ⟨j, u, hu⟩ := class_decomposition F v π hπ (inducingData.borel.coordinate g)
  let t := Lift F ζ hζ v (π ^ (j.val : ℤ)) *
    Lift F ζ hζ v (KPTameCompact.unitInclusion F v u)
  have he : inducingData.heisenberg.π g = inducingData.heisenberg.π t := by
    apply inducingData.cubeClassEquiv.injective
    rw [inducingData.cube_class, inducingData.cube_class]
    change _ = QuotientGroup.mk' (CubicCharacters.cubes (LocalField F v)ˣ)
      (inducingData.borel.coordinate (_ * _))
    rw [inducingData.borel.coordinate.map_mul]
    rw [inducingData.coordinate_lift (Lift F ζ hζ v (π ^ (j.val : ℤ))) _ rfl,
      inducingData.coordinate_lift (Lift F ζ hζ v (KPTameCompact.unitInclusion F v u)) _ rfl]
    exact hu
  have hc : g * t⁻¹ ∈ inducingData.heisenberg.C := by
    rw [← inducingData.heisenberg.quotient_kernel]
    change inducingData.heisenberg.π (g * t⁻¹) = 1
    simp [he]
  have huact : Action F ζ hζ v inducingData P (Lift F ζ hζ v (KPTameCompact.unitInclusion F v u)) b = b :=
    hb ⟨_, unit_lift_compact F ζ hζ v ht u⟩
  have hg : Action F ζ hζ v inducingData P g b =
      (inducingData.heisenberg.ω (inducingData.borel.weylCenter ⟨g * t⁻¹, hc⟩) : ℂ) •
      Action F ζ hζ v inducingData P (Lift F ζ hζ v (π ^ (j.val : ℤ))) b := by
    have h := hprops.2.2.2.1 ⟨g * t⁻¹, hc⟩ (Action F ζ hζ v inducingData P t b)
    simp only [Subgroup.coe_mk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at h
    rw [h]
    congr 1
    change Action F ζ hζ v inducingData P (_ * _) b = _
    rw [map_mul, Module.End.mul_apply, huact]
  change Action F ζ hζ v inducingData P g b ∈ S
  rw [hg]
  apply Submodule.smul_mem
  have hn : QPower F v (-(j.val : ℝ) / 6) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    exact Real.rpow_pos_of_pos (by
      change (Nat.card (IsLocalRing.ResidueField (valuation (LocalField F v)).integer) : ℝ) > 0
      exact_mod_cast Nat.card_pos) _
  have hj : Orbit F ζ hζ v inducingData P π b (j.val : ℤ) ∈ S := Submodule.subset_span ⟨j, rfl⟩
  have hj' := S.smul_mem (QPower F v (-(j.val : ℝ) / 6))⁻¹ hj
  simpa [Orbit, smul_smul, hn] using hj'

theorem normalized_orbit_basis
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (LocalField F v)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (π : LocalField F v)) = WithZero.exp (-1 : ℤ))
    (b : Fiber F ζ hζ v inducingData P) (hb : b ∈ TorusLine F ζ hζ v inducingData P ht) (hne : b ≠ 0) :
    ∃ B : Module.Basis (Fin 3) ℂ (Fiber F ζ hζ v inducingData P),
      ∀ i : Fin 3, B i = Orbit F ζ hζ v inducingData P π b (i.val : ℤ) := by
  let f : Fin 3 → Fiber F ζ hζ v inducingData P := fun i => Orbit F ζ hζ v inducingData P π b (i.val : ℤ)
  have hs : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    rw [normalized_span F ζ hζ v inducingData P ht π hπ b hb hne]
  have hd : Fintype.card (Fin 3) = Module.finrank ℂ (Fiber F ζ hζ v inducingData P) := by
    rw [dimension_three F ζ hζ v inducingData P ht]
    rfl
  refine ⟨basisOfTopLeSpanOfCardEqFinrank f hs hd, ?_⟩
  intro i
  exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank f hs hd) i
end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical

namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
variable (inducingData : CanonicalFiniteInducingData F ζ hζ v)
variable (P : Polarization inducingData.heisenberg)

def bZero (φ : Sections F ζ hζ v inducingData P) : Fiber F ζ hζ v inducingData P := φ.val 1

def bCoordinate (π : (LocalField F v)ˣ) (φ : Sections F ζ hζ v inducingData P) (j : ℤ) :=
  QPower F v (-(j : ℝ) / 6) •
    Action F ζ hζ v inducingData P (Lift F ζ hζ v (π ^ j)) (bZero F ζ hζ v inducingData P φ)

theorem bZero_ne_zero
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (φ : Sections F ζ hζ v inducingData P)
    (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht) (hne : φ ≠ 0) :
    bZero F ζ hζ v inducingData P φ ≠ 0 := by
  obtain ⟨E, hE⟩ := compact_evaluation_equiv F ζ hζ v inducingData P ht
  intro hz
  have he : E ⟨φ, hφ⟩ = 0 := by
    apply Subtype.ext
    exact (hE ⟨φ, hφ⟩).trans hz
  exact hne (congrArg Subtype.val (E.injective (he.trans (map_zero E).symm)))

theorem exists_unique_coordinateEquiv
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (LocalField F v)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (π : LocalField F v)) = WithZero.exp (-1 : ℤ))
    (φ : Sections F ζ hζ v inducingData P)
    (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht) (hne : φ ≠ 0) :
    ∃! Eφ : (Fin 3 → ℂ) ≃ₗ[ℂ] Fiber F ζ hζ v inducingData P,
      ∀ j : ℤ, Eφ (KPThreeShell.basis j) = bCoordinate F ζ hζ v inducingData P π φ j := by
  obtain ⟨E, hE⟩ := compact_evaluation_equiv F ζ hζ v inducingData P ht
  have hb : bZero F ζ hζ v inducingData P φ ∈ TorusLine F ζ hζ v inducingData P ht := by
    change φ.val 1 ∈ TorusLine F ζ hζ v inducingData P ht
    rw [← hE ⟨φ, hφ⟩]
    exact (E ⟨φ, hφ⟩).property
  exact KPExteriorSpherical.periodic_basis_coordinate_equiv
    (bCoordinate F ζ hζ v inducingData P π φ)
    (normalized_orbit_period F ζ hζ v inducingData P π hπ (bZero F ζ hζ v inducingData P φ))
    (normalized_orbit_basis F ζ hζ v inducingData P ht hgood π hπ
      (bZero F ζ hζ v inducingData P φ) hb (bZero_ne_zero F ζ hζ v inducingData P ht φ hφ hne))
end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualSpherical

namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualJacquet
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann ActualSpherical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
variable (inducingData : CanonicalFiniteInducingData F ζ hζ v)
variable (P : Polarization inducingData.heisenberg)
def uniformizerUnit (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) :
    (LocalField F v)ˣ :=
  Units.mk0 (π : LocalField F v) (by
    intro h
    apply hπ.ne_zero
    exact Subtype.ext h)

def sphericalTranslate (π : (valuation (LocalField F v)).integer)
    (hπ : Irreducible π) (φ : Sections F ζ hζ v inducingData P) (e : ℕ) :
    Sections F ζ hζ v inducingData P :=
  IMinus inducingData.borel P
    (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (uniformizerUnit F v π hπ ^ e))
    φ

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualJacquet
open scoped NumberField Valued ValuativeRel BigOperators ENNReal
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellRegion

open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
open ExteriorWhittakerValues.ActualSpherical KPExteriorUnitShellIntegrals ExteriorWhittakerValues.ActualJacquet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (v : HeightOneSpectrum (𝓞 F)) (inducingData : CanonicalFiniteInducingData F ζ hζ v)
  (P : Polarization inducingData.heisenberg)
variable [NormedAddCommGroup (Fiber F ζ hζ v inducingData P)]

local instance fiberUniformStep2 : UniformSpace (Fiber F ζ hζ v inducingData P) :=
  @PseudoMetricSpace.toUniformSpace _
    (inferInstance : PseudoMetricSpace (Fiber F ζ hζ v inducingData P))

local instance contributionTopologyStep2 : TopologicalSpace (Fiber F ζ hζ v inducingData P) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (inferInstance : PseudoMetricSpace (Fiber F ζ hζ v inducingData P)))

variable [NormedSpace ℂ (Fiber F ζ hζ v inducingData P)]

include P in
private lemma signed_upper (H : (LocalField F v)ˣ) :
    inducingData.borel.liftedW * KPPGLLocalCover.N F ζ hζ (Sum.inr v) H =
      KPPGLLocalCover.N F ζ hζ (Sum.inr v) (-(H⁻¹ : (LocalField F v)ˣ) : LocalField F v) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr v) (H⁻¹ ^ (2 : ℕ)) *
        KPPGLLocalCover.LowerN F ζ hζ (Sum.inr v) H⁻¹ := by
  rw [(inducingData.openCell P).weyl_eq]
  change (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1) *
    KPPGLLocalCover.W F ζ hζ (Sum.inr v)) * _ = _
  rw [mul_assoc, KPCorrectedBruhatLifts.quotient_weyl_upper]
  have hn : KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1) *
      KPPGLLocalCover.N F ζ hζ (Sum.inr v) (H⁻¹ : (LocalField F v)ˣ) =
    KPPGLLocalCover.N F ζ hζ (Sum.inr v) (-(H⁻¹ : (LocalField F v)ˣ) : LocalField F v) *
      KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1) := by
    symm
    simpa using KPCorrectedBruhatLifts.quotient_upper_diagonal F ζ hζ (Sum.inr v)
      (-(H⁻¹ : (LocalField F v)ˣ) : LocalField F v) (-1)
  rw [← mul_assoc, ← mul_assoc, hn]
  simp only [mul_assoc]
  rw [← mul_assoc (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1)),
    KPPGLLocalCover.A_mul,
    (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.1 (-1),
    (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.2 _ |>.2.1]
  simp

private lemma minus_torus_eval (φ : Sections F ζ hζ v inducingData P)
    (t : actualTorus F ζ hζ v) (g : ActualCover F ζ hζ v) :
    φ.val ((t : ActualCover F ζ hζ v) * g) =
    normPower (LocalField F v) (inducingData.borel.coordinate t) (1/2) •
      ActualSpherical.Action F ζ hζ v inducingData P t (φ.val g) := by
  rw [← inducingData.torus_full t, φ.property.1]
  simp [inducingAction, inducingScalar, deltaHalf, borelAction, ActualSpherical.Action,
    inducingData.borel.retract_torus, normPower]

private lemma lower_compact (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (x : (valuation (LocalField F v)).integer) :
    KPPGLLocalCover.LowerN F ζ hζ (Sum.inr v) x =
      actualGoodCompactSplit F ζ hζ v ht (KPStandardLocalRootLifts.integralLowerN F v x) := by
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v) _ =
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v) _
  apply congrArg (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v))
  exact KPStandardLocalRootLifts.LowerN_eq_compact F ζ hζ v ht x

private lemma neg_diagonal_commute (a : (LocalField F v)ˣ) :
    KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1) * KPPGLLocalCover.A F ζ hζ (Sum.inr v) a =
      KPPGLLocalCover.A F ζ hζ (Sum.inr v) a * KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1) := by
  have hc (x y : (LocalField F v)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr v) x y ^ 3 = 1 := by
    apply Subtype.ext
    exact (KPHilbert.B3 F ζ hζ (Sum.inr v) x y).property
  rw [KPPGLLocalCover.A_mul, KPPGLLocalCover.A_mul,
    KubotaDefectSymbolAlgebra.neg_one_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).1 hc,
    KubotaDefectSymbolAlgebra.neg_one_right _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1 hc]
  simp [mul_comm]
include P in
private lemma signed_diagonal (a : (LocalField F v)ˣ) :
    inducingData.borel.liftedW * KPPGLLocalCover.A F ζ hζ (Sum.inr v) a =
      KPPGLLocalCover.A F ζ hζ (Sum.inr v) a⁻¹ * inducingData.borel.liftedW := by
  rw [(inducingData.openCell P).weyl_eq]
  change (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1) * KPPGLLocalCover.W F ζ hζ (Sum.inr v)) * _ = _
  rw [mul_assoc, KPCorrectedBruhatLifts.quotient_weyl_diagonal, ← mul_assoc, neg_diagonal_commute]
  exact mul_assoc _ _ _

private lemma right_fixed (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (φ : Sections F ζ hζ v inducingData P) (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht)
    (k : ActualCover F ζ hζ v) (hk : k ∈ Compact F ζ hζ v ht)
    (g : ActualCover F ζ hζ v) :
    φ.val (g * k) =
      φ.val g := by
  exact congrArg (fun f : Sections F ζ hζ v inducingData P => f.val g)
    (hφ ⟨k, hk⟩)

private lemma central_eval (φ : Sections F ζ hζ v inducingData P)
    (z : rootsOfUnity 3 F) (g : ActualCover F ζ hζ v) :
    φ.val
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr v) z * g) =
      (ordinaryIota F ζ hζ z : ℂ) • φ.val g := by
  change φ.val (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr v) z * g) = _
  rw [← (inducingData.openCell P).central_eq z, φ.property.1]
  change inducingScalar inducingData.borel 0 (inducingData.borel.torus ((inducingData.openCell P).centralTorus z)) •
    borelAction inducingData.borel P .minus (inducingData.borel.torus ((inducingData.openCell P).centralTorus z))
      (φ.val g) = _
  have hs : inducingScalar inducingData.borel 0
      (inducingData.borel.torus ((inducingData.openCell P).centralTorus z)) = 1 := by
    simp [inducingScalar, deltaHalf, inducingData.borel.retract_torus,
      (inducingData.openCell P).central_coordinate, normPower, localAbs_one]
  rw [hs, one_smul, (inducingData.openCell P).genuine, inducingData.openCell_ordinary]

private lemma diagonal_product_eval (φ : Sections F ζ hζ v inducingData P)
    (a b : (LocalField F v)ˣ) (g : ActualCover F ζ hζ v) :
    φ.val
      (KPPGLLocalCover.A F ζ hζ (Sum.inr v) a *
        KPPGLLocalCover.A F ζ hζ (Sum.inr v) b * g) =
    KPSourceConvention.sourceC F ζ hζ (Sum.inr v) a b •
      φ.val
        (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (a * b) * g) := by
  rw [KPPGLLocalCover.A_mul, mul_assoc, central_eval F ζ hζ v inducingData P]
  rfl

private lemma uniformizer_normPower (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (j : ℤ) (s : ℝ) :
    normPower (LocalField F v) (uniformizerUnit F v π hπ ^ j) (s : ℂ) =
      QPower F v (-(j : ℝ) * s) := by
  have hq : 0 < (residueCardinality (LocalField F v) : ℝ) := by
    unfold residueCardinality
    exact_mod_cast Nat.card_pos
  have hpi : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (π : LocalField F v)) = WithZero.exp (-1 : ℤ) := by
    simpa only [WithZero.exp] using
      LocalFieldTheory.valueGroupWithZeroIsoInt_of_integerRing_irreducible (LocalField F v) π hπ
  have hlog : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) ↑(uniformizerUnit F v π hπ ^ j))) = -j := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀]
    change WithZero.log ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (π : LocalField F v))) ^ j) = _
    rw [hpi]
    simp
  unfold normPower localAbs
  rw [hlog, Real.log_rpow hq, QPower]
  change Complex.exp _ = ↑((residueCardinality (LocalField F v) : ℝ) ^ (-(j : ℝ) * s) : ℝ)
  rw [Real.rpow_def_of_pos hq, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem spherical_shell_integrand_evaluation
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ)
    (φ : Sections F ζ hζ v inducingData P) (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht)
    (χκ : MulChar (IsLocalRing.ResidueField (valuation (LocalField F v)).integer) ℂ)
    (hactual : ∀ u, unitCharacter χκ u = arithmeticUnitCharacter F ζ hζ v hgood u)
    (e : ℕ) (l : ℤ) (hl : 1 ≤ l)
    (u : LocalField F v) (hu : u ∈ KPTameGauss.integerUnitShell (LocalField F v)) :
    jacquetIntegrand F ζ hζ v inducingData P ψ (sphericalTranslate F ζ hζ v inducingData P π hπ φ e)
      ((π : LocalField F v) ^ ((e : ℤ) - l) * u) =
      (QPower F v ((e : ℝ) / 2 - (l : ℝ)) *
        shellIntegrand χκ ψ π e l u) •
        ActualSpherical.Action F ζ hζ v inducingData P
          (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ) + 2 * l)))
          (bZero F ζ hζ v inducingData P φ) := by
  classical
  obtain ⟨uO, huO, hunit⟩ := hu
  obtain ⟨U, hU⟩ := hunit
  have huval : ((U : (valuation (LocalField F v)).integer) : LocalField F v) = u := by
    rw [hU]; exact huO
  subst u
  rw [← huval]
  let p := uniformizerUnit F v π hπ
  let t := KPHilbert.integerUnitInclusion F v U
  let H := p ^ (-l) * t
  let j : ℤ := -(e : ℤ) + 2 * l
  have hp : (π : LocalField F v) ≠ 0 := p.ne_zero
  have hx : (π : LocalField F v) ^ ((e : ℤ) - l) * (U : LocalField F v) /
      ((p ^ e : (LocalField F v)ˣ) : LocalField F v) = (H : LocalField F v) := by
    dsimp [H, p, t, KPHilbert.integerUnitInclusion]
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
      uniformizerUnit, Units.val_mk0, div_eq_mul_inv]
    rw [mul_right_comm, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hp]
    congr 2; omega
  have hint : ((H⁻¹ : (LocalField F v)ˣ) : LocalField F v) ∈ (valuation (LocalField F v)).integer := by
    have hl0 : 0 ≤ l := by omega
    have hlN : (l.toNat : ℤ) = l := Int.toNat_of_nonneg hl0
    have he : ((H⁻¹ : (LocalField F v)ˣ) : LocalField F v) =
        (π : LocalField F v) ^ l.toNat * (U⁻¹ : LocalField F v) := by
      simp [H, p, t, KPHilbert.integerUnitInclusion, mul_comm, hlN, zpow_neg,
        uniformizerUnit, ← zpow_natCast, hlN]
    rw [he]
    exact (valuation (LocalField F v)).integer.mul_mem
      ((valuation (LocalField F v)).integer.pow_mem π.property _) (by
        have hi : ((U⁻¹ : (valuation (LocalField F v)).integerˣ) : LocalField F v) = (U : LocalField F v)⁻¹ := by
          simpa only [KPHilbert.integerUnitInclusion,
            LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits_apply, Units.val_inv_eq_inv_val]
            using congrArg Units.val ((KPHilbert.integerUnitInclusion F v).map_inv U)
        rw [← hi]
        exact (U⁻¹).val.property)
  have hab : p ^ (-(e : ℤ)) * H⁻¹ ^ (2 : ℕ) = p ^ j * KPHilbert.integerUnitInclusion F v (U⁻¹ ^ (2 : ℕ)) := by
    dsimp [H, j]
    rw [mul_inv, mul_pow, ← zpow_neg, neg_neg]
    rw [← mul_assoc, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    · congr 1; ring
  have hleft : (sphericalTranslate F ζ hζ v inducingData P π hπ φ e).val
      (inducingData.borel.liftedW * (inducingData.borel.upperRoot
        (Multiplicative.ofAdd ((π : LocalField F v) ^ ((e : ℤ) - l) * (U : LocalField F v))) : ActualCover F ζ hζ v)) =
      KPSourceConvention.sourceC F ζ hζ (Sum.inr v) (p ^ (-(e : ℤ))) (H⁻¹ ^ (2 : ℕ)) •
        φ.val
          (KPPGLLocalCover.A F ζ hζ (Sum.inr v)
            (p ^ j * KPHilbert.integerUnitInclusion F v (U⁻¹ ^ (2 : ℕ)))) := by
    change φ.val
      ((inducingData.borel.liftedW * _) * KPPGLLocalCover.A F ζ hζ (Sum.inr v) (p ^ e)) = _
    rw [(inducingData.openCell P).upper_eq]
    change φ.val
      ((inducingData.borel.liftedW * KPPGLLocalCover.N F ζ hζ (Sum.inr v) _) * _) = _
    rw [mul_assoc, KPCorrectedBruhatLifts.quotient_upper_diagonal, hx,
      ← mul_assoc, signed_diagonal F ζ hζ v inducingData P, mul_assoc,
      signed_upper F ζ hζ v inducingData P H]
    have hn : KPPGLLocalCover.A F ζ hζ (Sum.inr v) (p ^ e)⁻¹ *
        KPPGLLocalCover.N F ζ hζ (Sum.inr v) (-(H⁻¹ : (LocalField F v)ˣ) : LocalField F v) =
        KPPGLLocalCover.N F ζ hζ (Sum.inr v)
          (((p ^ e)⁻¹ : (LocalField F v)ˣ) * (-(H⁻¹ : (LocalField F v)ˣ) : LocalField F v)) *
          KPPGLLocalCover.A F ζ hζ (Sum.inr v) (p ^ e)⁻¹ := by
      symm
      simpa only [mul_div_cancel_left₀ _ (Units.ne_zero _)] using KPCorrectedBruhatLifts.quotient_upper_diagonal F ζ hζ (Sum.inr v)
        (((p ^ e)⁻¹ : (LocalField F v)ˣ) * (-(H⁻¹ : (LocalField F v)ˣ) : LocalField F v)) (p ^ e)⁻¹
    rw [← mul_assoc, ← mul_assoc, hn, mul_assoc, mul_assoc]
    have hroot (x : LocalField F v) : KPPGLLocalCover.N F ζ hζ (Sum.inr v) x =
        (inducingData.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ v) := by
      rw [(inducingData.openCell P).upper_eq]; rfl
    rw [hroot,
      φ.property.1, upperRoot_trivial]
    rw [show (p ^ e)⁻¹ = p ^ (-(e : ℤ)) by simp]
    rw [← mul_assoc, diagonal_product_eval F ζ hζ v inducingData P, hab]
    congr 1
    simp only [← Units.val_inv_eq_inv_val]
    rw [show KPPGLLocalCover.LowerN F ζ hζ (Sum.inr v) ((H⁻¹ : (LocalField F v)ˣ) : LocalField F v) =
      actualGoodCompactSplit F ζ hζ v ht (KPStandardLocalRootLifts.integralLowerN F v ⟨_, hint⟩)
      from lower_compact F ζ hζ v ht ⟨_, hint⟩]
    exact right_fixed F ζ hζ v inducingData P ht φ hφ _ ⟨_, rfl⟩ _
  have hvp : KPHilbert.ordinaryValuation F v p = 1 := by
    unfold KPHilbert.ordinaryValuation
    rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply]
    have hh := LocalFieldTheory.v_integerRingIrreducibleFieldUnit (LocalField F v) π hπ p rfl
    simpa using congrArg Neg.neg hh
  let c := arithmeticUnitCharacter F ζ hζ v hgood U
  have hc : c ≠ 0 := Units.ne_zero _
  have hc6 : c ^ (6 : ℕ) = 1 := by
    dsimp [c, arithmeticUnitCharacter]
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have hh : KPHilbert.residueSixCharacter F v ζ hζ hgood U ^ (6 : ℕ) = 1 := by
      apply Subtype.ext
      exact (KPHilbert.residueSixCharacter F v ζ hζ hgood U).property
    rw [hh, map_one, Units.val_one]
  let d : (valuation (LocalField F v)).integerˣ →* ℂˣ :=
    Units.map (χκ.toMonoidHom.comp (IsLocalRing.residue (valuation (LocalField F v)).integer).toMonoidHom)
  have hd (W : (valuation (LocalField F v)).integerˣ) :
      (d W : ℂ) = arithmeticUnitCharacter F ζ hζ v hgood W := hactual W
  have hchar : arithmeticUnitCharacter F ζ hζ v hgood (U⁻¹ ^ (2 : ℕ)) = c ^ (-2 : ℤ) := by
    rw [← hd, map_pow, map_inv, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hd]
    simp [c, zpow_neg, zpow_ofNat]
  have hchar1 : arithmeticUnitCharacter F ζ hζ v hgood 1 = 1 := by
    rw [← hd, map_one, Units.val_one]
  have hb : H⁻¹ ^ (2 : ℕ) = p ^ (2 * l) * KPHilbert.integerUnitInclusion F v (U⁻¹ ^ (2 : ℕ)) := by
    dsimp [H]
    rw [mul_inv, mul_pow, ← zpow_neg, neg_neg, ← zpow_natCast, ← zpow_mul]
    congr 1
    · congr 1; ring
  have hC1 : KPSourceConvention.sourceC F ζ hζ (Sum.inr v) (p ^ (-(e : ℤ)))
      (H⁻¹ ^ (2 : ℕ)) = c ^ (-4 * (e : ℤ)) := by
    rw [hb]
    have hh := KPSourceConvention.sourceC_valuation_units F ζ hζ v hgood p hvp
      1 (U⁻¹ ^ (2 : ℕ)) (-(e : ℤ)) (2*l)
    change KPSourceConvention.sourceC F ζ hζ (Sum.inr v)
      (p ^ (-(e : ℤ)) * KPHilbert.integerUnitInclusion F v 1)
      (p ^ (2*l) * KPHilbert.integerUnitInclusion F v (U⁻¹ ^ (2 : ℕ))) =
      arithmeticUnitCharacter F ζ hζ v hgood 1 ^ (2*(2*l)) *
      arithmeticUnitCharacter F ζ hζ v hgood (U⁻¹ ^ (2 : ℕ)) ^ (-2 * (-(e : ℤ))) at hh
    simp only [map_one, mul_one, hchar1, one_zpow, one_mul, hchar1, one_zpow, hchar, ← zpow_mul] at hh
    convert hh using 1 <;> congr 1 <;> ring
  have hC2 : KPSourceConvention.sourceC F ζ hζ (Sum.inr v) (p ^ j)
      (KPHilbert.integerUnitInclusion F v (U⁻¹ ^ (2 : ℕ))) = c ^ (4 * j) := by
    have hh := KPSourceConvention.sourceC_valuation_units F ζ hζ v hgood p hvp
      1 (U⁻¹ ^ (2 : ℕ)) j 0
    change KPSourceConvention.sourceC F ζ hζ (Sum.inr v)
      (p ^ j * KPHilbert.integerUnitInclusion F v 1)
      (p ^ 0 * KPHilbert.integerUnitInclusion F v (U⁻¹ ^ (2 : ℕ))) =
      arithmeticUnitCharacter F ζ hζ v hgood 1 ^ (2*0) *
      arithmeticUnitCharacter F ζ hζ v hgood (U⁻¹ ^ (2 : ℕ)) ^ (-2 * j) at hh
    simp only [map_one, mul_one, zpow_zero, one_mul, hchar1, one_zpow, hchar, ← zpow_mul] at hh
    convert hh using 1 <;> congr 1 <;> ring
  have huA : KPPGLLocalCover.A F ζ hζ (Sum.inr v)
      (KPHilbert.integerUnitInclusion F v (U⁻¹ ^ (2 : ℕ))) ∈ Compact F ζ hζ v ht := by
    refine ⟨KPStandardLocalRootLifts.integralA F v (U⁻¹ ^ (2 : ℕ)), ?_⟩
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v) _ = _
    rw [KPPGLLocalCover.A, KPStandardLocalRootLifts.A_eq_compact F ζ hζ v ht]
    rfl
  have heval := diagonal_product_eval F ζ hζ v inducingData P φ (p ^ j)
    (KPHilbert.integerUnitInclusion F v (U⁻¹ ^ (2 : ℕ))) 1
  simp only [mul_one] at heval
  rw [right_fixed F ζ hζ v inducingData P ht φ hφ _ huA, hC2] at heval
  have hn := minus_torus_eval F ζ hζ v inducingData P φ (Lift F ζ hζ v (p ^ j)) 1
  simp only [mul_one] at hn
  rw [inducingData.coordinate_lift (Lift F ζ hζ v (p ^ j)) (p ^ j) rfl] at hn
  change φ.val (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (p ^ j)) = _ at hn
  rw [hn] at heval
  change normPower (LocalField F v) (p ^ j) (1/2) •
    ActualSpherical.Action F ζ hζ v inducingData P (Lift F ζ hζ v (p ^ j)) (bZero F ζ hζ v inducingData P φ) = _ at heval
  have hval := congrArg (fun b : Fiber F ζ hζ v inducingData P => c ^ (-(4*j)) • b) heval
  simp only [smul_smul, ← zpow_add₀ hc] at hval
  simp only [neg_add_cancel, zpow_zero, one_smul] at hval
  have hphase : c ^ (-4 * (e : ℤ)) * c ^ (-(4*j)) = c ^ (-2*l) := by
    rw [← zpow_add₀ hc]
    have hexp : -4 * (e : ℤ) + -(4*j) = -2*l + 6*(-l) := by dsimp [j]; ring
    rw [hexp, zpow_add₀ hc]
    rw [zpow_mul c 6 (-l)]
    norm_num only [zpow_ofNat, hc6, one_zpow, mul_one]
  unfold jacquetIntegrand
  rw [hleft, hC1, ← hval, smul_smul, smul_smul]
  rw [mul_assoc (star _), ← mul_assoc (c ^ _), hphase]
  have hnorm := uniformizer_normPower F v π hπ j (1/2)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hnorm
  rw [hnorm]
  have hexp : -(j : ℝ) * (1/2) = (e : ℝ)/2 - (l : ℝ) := by dsimp [j]; push_cast; ring
  rw [hexp]
  unfold shellIntegrand
  have hmem : (U : LocalField F v) ∈ ((valuation (LocalField F v)).integer : Set (LocalField F v)) := U.val.property
  rw [dif_pos hmem]
  have hχ : χκ (IsLocalRing.residue _ (U : (valuation (LocalField F v)).integer)) = c := hactual U
  rw [hχ]
  congr 1
  ring

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellRegion

namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualJacquet
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann ActualSpherical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
variable (inducingData : CanonicalFiniteInducingData F ζ hζ v)
variable (P : Polarization inducingData.heisenberg)
variable (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]
abbrev sphericalBall (π : (valuation (LocalField F v)).integer) (e : ℕ) :=
  KPExteriorActualJacquetShellsRaw.sphericalBall F v π e
abbrev sphericalShell (π : (valuation (LocalField F v)).integer) (e : ℕ) (l : ℤ) :=
  KPExteriorActualJacquetShellsRaw.sphericalShell F v π e l

variable [NormedAddCommGroup (Fiber F ζ hζ v inducingData P)]

local instance contributionTopology : TopologicalSpace (Fiber F ζ hζ v inducingData P) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _ (inferInstance : PseudoMetricSpace (Fiber F ζ hζ v inducingData P)))

variable [NormedSpace ℂ (Fiber F ζ hζ v inducingData P)]

def ballContribution (ψ : AddChar (LocalField F v) ℂ)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (φ : Sections F ζ hζ v inducingData P) (e : ℕ) : Fiber F ζ hζ v inducingData P :=
  ∫ x in sphericalBall F v π e,
    jacquetIntegrand F ζ hζ v inducingData P ψ (sphericalTranslate F ζ hζ v inducingData P π hπ φ e) x ∂μ

def shellContribution (ψ : AddChar (LocalField F v) ℂ)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (φ : Sections F ζ hζ v inducingData P) (e : ℕ) (l : ℤ) : Fiber F ζ hζ v inducingData P :=
  ∫ x in sphericalShell F v π e l,
    jacquetIntegrand F ζ hζ v inducingData P ψ (sphericalTranslate F ζ hζ v inducingData P π hπ φ e) x ∂μ

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualJacquet
open scoped NumberField Valued ValuativeRel BigOperators ENNReal
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellRegion

open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
open ExteriorWhittakerValues.ActualSpherical KPExteriorUnitShellIntegrals ExteriorWhittakerValues.ActualJacquet

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (v : HeightOneSpectrum (𝓞 F)) (inducingData : CanonicalFiniteInducingData F ζ hζ v)
  (P : Polarization inducingData.heisenberg)
variable (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]
variable (N : AddGroupNorm (Fiber F ζ hζ v inducingData P))
variable (hN : ∀ (c : ℂ) (b : Fiber F ζ hζ v inducingData P), N (c • b) = ‖c‖ * N b)

private lemma qPower_mul (a b : ℝ) :
    QPower F v a *
      QPower F v b =
        QPower F v (a + b) := by
  have hq : 0 < (residueCardinality (LocalField F v) : ℝ) := by
    unfold residueCardinality
    exact_mod_cast Nat.card_pos
  unfold QPower
  rw [← Complex.ofReal_mul]
  congr 1
  exact (Real.rpow_add hq a b).symm

theorem ball_contribution_of_constant_value
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (φ : Sections F ζ hζ v inducingData P) (e : ℕ)
    (hpoint : ∀ x : LocalField F v, x ∈ sphericalBall F v π e →
      jacquetIntegrand F ζ hζ v inducingData P ψ (sphericalTranslate F ζ hζ v inducingData P π hπ φ e) x =
        QPower F v ((e : ℝ) / 2) •
          ActualSpherical.Action F ζ hζ v inducingData P
            (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ))))
            (bZero F ζ hζ v inducingData P φ))
    (hmass : (μ (sphericalBall F v π e)).toReal =
      (residueCardinality (LocalField F v) : ℝ) ^ (-(e : ℝ))) :
    letI := CompatibleFiniteNorm.normedAddCommGroup N
    letI := CompatibleFiniteNorm.normedSpace N hN
    letI := CompatibleFiniteNorm.topology N
    ballContribution F ζ hζ v inducingData P μ ψ π hπ φ e =
      QPower F v (-2 * (e : ℝ) / 3) •
        bCoordinate F ζ hζ v inducingData P (uniformizerUnit F v π hπ) φ (-(e : ℤ)) := by
  let := CompatibleFiniteNorm.normedAddCommGroup N
  let := CompatibleFiniteNorm.normedSpace N hN
  let : UniformSpace (Fiber F ζ hζ v inducingData P) :=
    (CompatibleFiniteNorm.normedAddCommGroup N).toMetricSpace.toPseudoMetricSpace.toUniformSpace
  let : TopologicalSpace (Fiber F ζ hζ v inducingData P) := CompatibleFiniteNorm.topology N
  let := inducingData.finiteD
  let : Module.Finite ℂ (Fiber F ζ hζ v inducingData P) :=
    tau_moduleFinite inducingData.heisenberg P
  let : CompleteSpace (Fiber F ζ hζ v inducingData P) := FiniteDimensional.complete ℂ _
  unfold ballContribution
  rw [setIntegral_congr_fun
    (KPExteriorActualJacquetShellsGeometry.measurableSet_sphericalBall F v π hπ e)
    hpoint, setIntegral_const]
  change (μ (sphericalBall F v π e)).toReal • _ = _
  rw [hmass, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  change (QPower F v (-(e : ℝ)) *
    QPower F v ((e : ℝ) / 2)) • _ = _
  rw [qPower_mul]
  unfold bCoordinate
  rw [smul_smul, qPower_mul]
  simp only [Int.cast_neg, Int.cast_natCast]
  congr 2
  ring

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellRegion
open scoped NumberField Valued ValuativeRel BigOperators ENNReal
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellRegion

open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
open ExteriorWhittakerValues.ActualSpherical KPExteriorUnitShellIntegrals ExteriorWhittakerValues.ActualJacquet

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (v : HeightOneSpectrum (𝓞 F)) (inducingData : CanonicalFiniteInducingData F ζ hζ v)
  (P : Polarization inducingData.heisenberg)
variable (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]
variable (N : AddGroupNorm (Fiber F ζ hζ v inducingData P))
  (hN : ∀ (c : ℂ) (b : Fiber F ζ hζ v inducingData P), N (c • b) = ‖c‖ * N b)

theorem compatible_shell_contribution_of_scaled_value
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (φ : Sections F ζ hζ v inducingData P)
    (χκ : MulChar (IsLocalRing.ResidueField (valuation (LocalField F v)).integer) ℂ)
    (e : ℕ) (l : ℤ)
    (hpoint : ∀ u : LocalField F v, u ∈ KPTameGauss.integerUnitShell (LocalField F v) →
      jacquetIntegrand F ζ hζ v inducingData P ψ (sphericalTranslate F ζ hζ v inducingData P π hπ φ e)
        ((π : LocalField F v) ^ ((e : ℤ) - l) * u) =
        (QPower F v ((e : ℝ) / 2 - (l : ℝ)) *
          shellIntegrand χκ ψ π e l u) •
          ActualSpherical.Action F ζ hζ v inducingData P
            (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ) + 2 * l)))
            (bZero F ζ hζ v inducingData P φ)) :
    letI := CompatibleFiniteNorm.normedAddCommGroup N
    letI := CompatibleFiniteNorm.normedSpace N hN
    letI : UniformSpace (Fiber F ζ hζ v inducingData P) :=
      (CompatibleFiniteNorm.normedAddCommGroup N).toMetricSpace.toPseudoMetricSpace.toUniformSpace
    letI : TopologicalSpace (Fiber F ζ hζ v inducingData P) := CompatibleFiniteNorm.topology N
    shellContribution F ζ hζ v inducingData P μ ψ π hπ φ e l =
      (QPower F v (-2 * (e : ℝ) / 3) *
        QPower F v ((l : ℝ) / 3) *
          A μ χκ ψ π e l) •
        bCoordinate F ζ hζ v inducingData P (uniformizerUnit F v π hπ) φ (-(e : ℤ) + 2 * l) := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI : UniformSpace (Fiber F ζ hζ v inducingData P) :=
    (CompatibleFiniteNorm.normedAddCommGroup N).toMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace (Fiber F ζ hζ v inducingData P) := CompatibleFiniteNorm.topology N
  letI : Module.Finite ℂ (Fiber F ζ hζ v inducingData P) := tau_moduleFinite _ P
  letI : CompleteSpace (Fiber F ζ hζ v inducingData P) := FiniteDimensional.complete ℂ _
  classical
  let K := LocalField F v
  let a : K := (π : K) ^ ((e : ℤ) - l)
  have ha : a ≠ 0 := zpow_ne_zero _ (uniformizerUnit F v π hπ).ne_zero
  let S := KPTameGauss.integerUnitShell K
  let f := jacquetIntegrand F ζ hζ v inducingData P ψ
    (sphericalTranslate F ζ hζ v inducingData P π hπ φ e)
  let q : ℝ := residueCardinality K
  have hq : 0 < q := by
    dsimp [q, residueCardinality]
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField (valuation K).integer))
  have hpi : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ) :=
    LocalFieldTheory.valueGroupWithZeroIsoInt_of_integerRing_irreducible K π hπ
  have habs : IntrinsicHaarScaling.abs K a⁻¹ = q ^ ((e : ℤ) - l) := by
    simp only [IntrinsicHaarScaling.abs, if_neg (inv_ne_zero ha), a,
      map_inv₀, map_zpow₀, hpi, WithZero.log_inv, WithZero.log_zpow]
    simp only [WithZero.log_exp, Int.zsmul_eq_mul, mul_neg, mul_one, neg_neg]
    rfl
  have hpre : (fun x : K => a⁻¹ * x) ⁻¹' S = sphericalShell F v π e l := by
    ext x
    change a⁻¹ * x ∈ S ↔ ∃ u ∈ S, x = a * u
    constructor
    · intro hx
      exact ⟨a⁻¹ * x, hx, by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩
    · rintro ⟨u, hu, rfl⟩
      simpa only [← mul_assoc, inv_mul_cancel₀ ha, one_mul] using hu
  have H := (Homeomorph.mulLeft₀ a⁻¹ (inv_ne_zero ha)).measurableEmbedding.setIntegral_map
    (μ := μ) (fun u : K => f (a * u)) S
  change (∫ u in S, f (a * u) ∂Measure.map (fun x : K => a⁻¹ * x) μ) =
    ∫ x in (fun x : K => a⁻¹ * x) ⁻¹' S, f (a * (a⁻¹ * x)) ∂μ at H
  rw [IntrinsicHaarScaling.map_mul K μ a⁻¹ (inv_ne_zero ha),
    Measure.restrict_smul, integral_smul_measure, habs, hpre] at H
  simp only [← mul_assoc, mul_inv_cancel₀ ha, one_mul] at H
  have hc : ((ENNReal.ofReal (q ^ ((e : ℤ) - l)))⁻¹).toReal =
      q ^ ((l : ℝ) - (e : ℝ)) := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt (zpow_pos hq _)),
      ← zpow_neg, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  rw [hc] at H

  change (∫ x in sphericalShell F v π e l, f x ∂μ) = _
  rw [← H]
  have hS : MeasurableSet S := by
    have hs : sphericalShell F v π 0 0 = S := by
      ext x
      change (∃ u ∈ S, x = (π : K) ^ ((0 : ℤ) - 0) * u) ↔ x ∈ S
      simp only [sub_self, zpow_zero, one_mul]
      constructor
      · rintro ⟨u, hu, rfl⟩; exact hu
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [← hs]
    exact KPExteriorActualJacquetShellsGeometry.measurableSet_sphericalShell F v π hπ 0 0
  have hint : (∫ u in S, f (a * u) ∂μ) =
      (QPower F v ((e : ℝ) / 2 - (l : ℝ)) *
        A μ χκ ψ π e l) •
        ActualSpherical.Action F ζ hζ v inducingData P
          (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ) + 2 * l)))
          (bZero F ζ hζ v inducingData P φ) := by
    calc
      _ = ∫ u in S, (QPower F v
          ((e : ℝ) / 2 - (l : ℝ)) * shellIntegrand χκ ψ π e l u) •
          ActualSpherical.Action F ζ hζ v inducingData P
            (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ) + 2 * l)))
            (bZero F ζ hζ v inducingData P φ) ∂μ := by
        apply setIntegral_congr_fun hS
        exact hpoint
      _ = _ := by
        rw [integral_smul_const, integral_const_mul]
        rfl
  rw [hint, bCoordinate, smul_smul]
  have hscalar : ((q ^ ((l : ℝ) - (e : ℝ)) : ℝ) : ℂ) *
      (QPower F v ((e : ℝ) / 2 - (l : ℝ)) *
        A μ χκ ψ π e l) =
      (QPower F v (-2 * (e : ℝ) / 3) *
        QPower F v ((l : ℝ) / 3) *
        A μ χκ ψ π e l) *
        QPower F v (-((-(e : ℤ) + 2 * l : ℤ) : ℝ) / 6) := by
    have hp (x y : ℝ) : QPower F v x *
        QPower F v y =
        QPower F v (x + y) := by
      unfold QPower
      change ((q ^ x : ℝ) : ℂ) * ((q ^ y : ℝ) : ℂ) = ((q ^ (x + y) : ℝ) : ℂ)
      rw [Real.rpow_add hq, Complex.ofReal_mul]
    change QPower F v ((l : ℝ) - (e : ℝ)) *
      (QPower F v ((e : ℝ) / 2 - (l : ℝ)) * _) = _
    rw [← mul_assoc]
    rw [hp]
    rw [mul_assoc _ (A μ χκ ψ π e l), mul_comm (A μ χκ ψ π e l),
      ← mul_assoc, hp, hp]
    congr 2
    push_cast
    ring
  have hvec := congrArg
    (fun c : ℂ => c • ActualSpherical.Action F ζ hζ v inducingData P
      (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ) + 2 * l)))
      (bZero F ζ hζ v inducingData P φ)) hscalar
  simpa only [← Complex.coe_smul, smul_smul] using hvec

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellRegion
open scoped NumberField Valued ValuativeRel BigOperators ENNReal
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellIntegral
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
open ExteriorWhittakerValues.ActualSpherical KPExteriorUnitShellIntegrals ExteriorWhittakerValues.ActualJacquet
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (v : HeightOneSpectrum (𝓞 F)) (inducingData : CanonicalFiniteInducingData F ζ hζ v)
  (P : Polarization inducingData.heisenberg)
variable (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]
variable (hμ : μ ((valuation (LocalField F v)).integer : Set (LocalField F v)) = 1)
private lemma compact_N (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (u : (valuation (LocalField F v)).integer) :
    KPPGLLocalCover.N F ζ hζ (Sum.inr v) u ∈ Compact F ζ hζ v ht := by
  refine ⟨KPStandardLocalRootLifts.integralN F v u, ?_⟩
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v) _ = _
  rw [KPPGLLocalCover.N, KPStandardLocalRootLifts.N_eq_compact F ζ hζ v ht u]
  rfl
private lemma compact_A (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (u : (valuation (LocalField F v)).integerˣ) :
    KPPGLLocalCover.A F ζ hζ (Sum.inr v) (KPTameCompact.unitInclusion F v u) ∈
      Compact F ζ hζ v ht := by
  refine ⟨KPStandardLocalRootLifts.integralA F v u, ?_⟩
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v) _ = _
  rw [KPPGLLocalCover.A, KPStandardLocalRootLifts.A_eq_compact F ζ hζ v ht u]
  rfl
private lemma compact_W (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :
    KPPGLLocalCover.W F ζ hζ (Sum.inr v) ∈ Compact F ζ hζ v ht := by
  refine ⟨KPStandardLocalRootLifts.integralW F v, ?_⟩
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v) _ = _
  rw [KPPGLLocalCover.W, KPStandardLocalRootLifts.W_eq_compact F ζ hζ v ht]
  rfl
private lemma signedW_eq : KPRankOneOpenCellKernel.signedWeyl F ζ hζ v =
    KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1) * KPPGLLocalCover.W F ζ hζ (Sum.inr v) := by
  rfl
include P in
private lemma compact_signedW (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :
    inducingData.borel.liftedW ∈ Compact F ζ hζ v ht := by
  rw [(inducingData.openCell P).weyl_eq, signedW_eq]
  apply Subgroup.mul_mem
  · exact compact_A F ζ hζ v ht (-1)
  · exact compact_W F ζ hζ v ht
private lemma right_fixed (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (φ : Sections F ζ hζ v inducingData P) (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht)
    (k : ActualCover F ζ hζ v) (hk : k ∈ Compact F ζ hζ v ht)
    (g : ActualCover F ζ hζ v) :
    φ.val (g * k) =
      φ.val g := by
  exact congrArg (fun f : Sections F ζ hζ v inducingData P => f.val g)
    (hφ ⟨k, hk⟩)
private lemma minus_eval (φ : Sections F ζ hζ v inducingData P)
    (t : actualTorus F ζ hζ v) (g : ActualCover F ζ hζ v) :
    φ.val ((t : ActualCover F ζ hζ v) * g) =
    normPower (LocalField F v) (inducingData.borel.coordinate t) (1/2) •
      ActualSpherical.Action F ζ hζ v inducingData P t (φ.val g) := by
  rw [← inducingData.torus_full t, φ.property.1]
  simp [inducingAction, inducingScalar, deltaHalf, borelAction, ActualSpherical.Action,
    inducingData.borel.retract_torus, normPower]
private lemma neg_diagonal_commute (a : (LocalField F v)ˣ) :
    KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1) * KPPGLLocalCover.A F ζ hζ (Sum.inr v) a =
      KPPGLLocalCover.A F ζ hζ (Sum.inr v) a * KPPGLLocalCover.A F ζ hζ (Sum.inr v) (-1) := by
  have hc (x y : (LocalField F v)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr v) x y ^ 3 = 1 := by
    apply Subtype.ext
    exact (KPHilbert.B3 F ζ hζ (Sum.inr v) x y).property
  rw [KPPGLLocalCover.A_mul, KPPGLLocalCover.A_mul,
    KubotaDefectSymbolAlgebra.neg_one_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).1 hc,
    KubotaDefectSymbolAlgebra.neg_one_right _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1 hc]
  simp [mul_comm]
include P in
private lemma signed_diagonal (a : (LocalField F v)ˣ) :
    inducingData.borel.liftedW * KPPGLLocalCover.A F ζ hζ (Sum.inr v) a =
      KPPGLLocalCover.A F ζ hζ (Sum.inr v) a⁻¹ * inducingData.borel.liftedW := by
  rw [(inducingData.openCell P).weyl_eq, signedW_eq, mul_assoc,
    KPCorrectedBruhatLifts.quotient_weyl_diagonal, ← mul_assoc, neg_diagonal_commute]
  exact mul_assoc _ _ _
theorem spherical_ball_section_evaluation (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (φ : Sections F ζ hζ v inducingData P) (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) (e : ℕ)
    (u : (valuation (LocalField F v)).integer) :
    (sphericalTranslate F ζ hζ v inducingData P π hπ φ e).val
      (inducingData.borel.liftedW * (inducingData.borel.upperRoot
        (Multiplicative.ofAdd ((π : LocalField F v)^e * u)) : ActualCover F ζ hζ v)) =
    normPower (LocalField F v) (uniformizerUnit F v π hπ ^ (-(e : ℤ))) (1/2) •
      ActualSpherical.Action F ζ hζ v inducingData P (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ))))
        (bZero F ζ hζ v inducingData P φ) := by
  change φ.val
    ((inducingData.borel.liftedW * _) * KPPGLLocalCover.A F ζ hζ (Sum.inr v) _) = _
  rw [(inducingData.openCell P).upper_eq, show KPRankOneOpenCellKernel.nLift F ζ hζ v = KPPGLLocalCover.N F ζ hζ (Sum.inr v) from rfl, mul_assoc,
    KPCorrectedBruhatLifts.quotient_upper_diagonal, ← mul_assoc, signed_diagonal F ζ hζ v inducingData P]
  have hp : (π : LocalField F v) ≠ 0 := (uniformizerUnit F v π hπ).ne_zero
  have hu : (π : LocalField F v)^e * (u : LocalField F v) /
      ↑(uniformizerUnit F v π hπ ^ e) = (u : LocalField F v) := by
    simp [uniformizerUnit, hp]
  rw [hu, mul_assoc]
  have ha : (uniformizerUnit F v π hπ ^ e)⁻¹ =
      uniformizerUnit F v π hπ ^ (-(e : ℤ)) := by simp
  rw [ha]
  have heval := minus_eval F ζ hζ v inducingData P φ
    (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ))))
    (inducingData.borel.liftedW * KPPGLLocalCover.N F ζ hζ (Sum.inr v) u)
  change φ.val (KPPGLLocalCover.A F ζ hζ (Sum.inr v) _ * _) = _ at heval
  rw [heval]
  have hf := right_fixed F ζ hζ v inducingData P ht φ hφ _
    ((Compact F ζ hζ v ht).mul_mem (compact_signedW F ζ hζ v inducingData P ht)
      (compact_N F ζ hζ v ht u)) 1
  simp only [one_mul] at hf
  rw [hf]
  have hcoord := inducingData.coordinate_lift
    (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ))))
    (uniformizerUnit F v π hπ ^ (-(e : ℤ))) rfl
  rw [hcoord]
  rfl
private lemma pi_value (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (π : LocalField F v)) = WithZero.exp (-1 : ℤ) := by
  let E := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
  have hlt : valuation (LocalField F v) (π : LocalField F v) < 1 :=
    (Valuation.integer.integers (valuation (LocalField F v))).valuation_irreducible_lt_one hπ
  have hpos : E (valuation (LocalField F v) (π : LocalField F v)) ≠ 0 := by
    intro he
    have hzero := E.injective (he.trans (map_zero E).symm)
    exact (valuation (LocalField F v)).ne_zero_iff.mpr (uniformizerUnit F v π hπ).ne_zero hzero
  have hneg : WithZero.log (E (valuation (LocalField F v) (π : LocalField F v))) < 0 := by
    have he := E.strictMono hlt
    rw [map_one, ← WithZero.exp_log hpos, ← WithZero.exp_zero, WithZero.exp_lt_exp] at he
    exact he
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (E.symm (WithZero.exp (-1 : ℤ)))
  have hv : valuation (LocalField F v) x < 1 := by
    apply E.toOrderIso.lt_iff_lt.mp
    change E (valuation (LocalField F v) x) < E 1
    rw [hx, E.apply_symm_apply, map_one]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hm : (⟨x, hv.le⟩ : (valuation (LocalField F v)).integer) ∈
      IsLocalRing.maximalIdeal ((valuation (LocalField F v)).integer) := by
    intro hu
    have hv1 := (Valuation.integer.integers (valuation (LocalField F v))).isUnit_iff_valuation_eq_one.mp hu
    exact hv.ne hv1
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  obtain ⟨u, hu⟩ := hm
  have hxle : valuation (LocalField F v) x ≤ valuation (LocalField F v) (π : LocalField F v) := by
    have he := congrArg (fun t : (valuation (LocalField F v)).integer => (t : LocalField F v)) hu
    change x = (π : LocalField F v) * (u : LocalField F v) at he
    rw [he, map_mul]
    exact mul_le_of_le_one_right bot_le u.property
  have hle := E.toOrderIso.monotone hxle
  change E (valuation (LocalField F v) x) ≤ E (valuation (LocalField F v) (π : LocalField F v)) at hle
  rw [hx, E.apply_symm_apply, ← WithZero.exp_log hpos, WithZero.exp_le_exp] at hle
  have hlog : WithZero.log (E (valuation (LocalField F v) (π : LocalField F v))) = -1 := by omega
  rw [← WithZero.exp_log hpos, hlog]
theorem uniformizer_normPower (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (j : ℤ) (s : ℝ) :
    normPower (LocalField F v) (uniformizerUnit F v π hπ ^ j) (s : ℂ) =
      QPower F v (-(j : ℝ) * s) := by
  have hq : 0 < (residueCardinality (LocalField F v) : ℝ) := by
    unfold residueCardinality
    exact_mod_cast Nat.card_pos
  have hlog : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) ↑(uniformizerUnit F v π hπ ^ j))) = -j := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀]
    change WithZero.log ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (π : LocalField F v))) ^ j) = _
    rw [pi_value F v π hπ]
    simp
  unfold normPower localAbs
  rw [hlog, Real.log_rpow hq, QPower]
  change Complex.exp _ = ↑((residueCardinality (LocalField F v) : ℝ) ^ (-(j : ℝ) * s) : ℝ)
  rw [Real.rpow_def_of_pos hq]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring
variable (N : AddGroupNorm (Fiber F ζ hζ v inducingData P))
variable (hN : ∀ (c : ℂ) (b : Fiber F ζ hζ v inducingData P), N (c • b) = ‖c‖ * N b)

theorem spherical_ball_integrand_evaluation (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (φ : Sections F ζ hζ v inducingData P) (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hcond : ConductorZero ψ π) (e : ℕ)
    (x : LocalField F v) (hx : x ∈ sphericalBall F v π e) :
    jacquetIntegrand F ζ hζ v inducingData P ψ (sphericalTranslate F ζ hζ v inducingData P π hπ φ e) x =
      QPower F v ((e : ℝ)/2) •
        ActualSpherical.Action F ζ hζ v inducingData P (Lift F ζ hζ v (uniformizerUnit F v π hπ ^ (-(e : ℤ))))
          (bZero F ζ hζ v inducingData P φ) := by
  obtain ⟨u, rfl⟩ := hx
  have hphase : ψ ((π : LocalField F v)^e * u) = 1 := by
    exact hcond.1 (π ^ e * u)
  unfold jacquetIntegrand
  rw [hphase, star_one, one_smul, spherical_ball_section_evaluation F ζ hζ v inducingData P ht φ hφ π hπ e u]
  have hn := uniformizer_normPower F v π hπ (-(e : ℤ)) (1/2)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hn
  rw [hn]
  congr 1
  congr 1
  push_cast
  ring
include hμ in
theorem spherical_ball_mass_toReal (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) (e : ℕ) :
    (μ (sphericalBall F v π e)).toReal =
      (residueCardinality (LocalField F v) : ℝ) ^ (-(e : ℝ)) := by
  let c : LocalField F v := (π : LocalField F v) ^ e
  have hc : c ≠ 0 := pow_ne_zero e (uniformizerUnit F v π hπ).ne_zero
  have he : sphericalBall F v π e = (fun x : LocalField F v => c * x) ''
      ((valuation (LocalField F v)).integer : Set (LocalField F v)) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨u, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩
  have hB : MeasurableSet (sphericalBall F v π e) := by
    rw [he]
    exact (Homeomorph.mulLeft₀ c hc).isClosedEmbedding.measurableEmbedding.measurableSet_image'
      (valuation (LocalField F v)).isClosed_integer.measurableSet
  have habs : IntrinsicHaarScaling.abs (LocalField F v) c =
      (residueCardinality (LocalField F v) : ℝ) ^ (-(e : ℝ)) := by
    unfold IntrinsicHaarScaling.abs
    rw [if_neg hc]
    change (residueCardinality (LocalField F v) : ℝ) ^ WithZero.log
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
        (valuation (LocalField F v) ((π : LocalField F v)^e))) = _
    rw [map_pow, map_pow, pi_value F v π hπ]
    simp [← Real.rpow_intCast]
  have hpre : (fun x : LocalField F v => c * x) ⁻¹' sphericalBall F v π e =
      ((valuation (LocalField F v)).integer : Set (LocalField F v)) := by
    rw [he]
    exact Set.preimage_image_eq _ (mul_right_injective₀ hc)
  have hm := congrArg (fun μ : Measure (LocalField F v) => μ (sphericalBall F v π e))
    (IntrinsicHaarScaling.map_mul (LocalField F v) μ c hc)
  rw [Measure.map_apply (by fun_prop) hB, hpre, hμ, Measure.smul_apply,
    smul_eq_mul, habs] at hm
  have hq : 0 < (residueCardinality (LocalField F v) : ℝ) := by
    unfold residueCardinality
    exact_mod_cast Nat.card_pos
  have hpos : 0 < (residueCardinality (LocalField F v) : ℝ) ^ (-(e : ℝ)) := Real.rpow_pos_of_pos hq _
  have hmul := congrArg (fun x : ℝ≥0∞ =>
    ENNReal.ofReal ((residueCardinality (LocalField F v) : ℝ) ^ (-(e : ℝ))) * x) hm
  rw [← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hpos)
    ENNReal.ofReal_ne_top, one_mul, mul_one] at hmul
  rw [← hmul, ENNReal.toReal_ofReal hpos.le]

include P

include hμ in

theorem spherical_region_evaluation
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (φ : Sections F ζ hζ v inducingData P)
    (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht) (hne : φ ≠ 0) (e : ℕ) :
    letI := CompatibleFiniteNorm.normedAddCommGroup N
    letI := CompatibleFiniteNorm.normedSpace N hN
    letI := CompatibleFiniteNorm.topology N
    (ballContribution F ζ hζ v inducingData P μ ψ π hπ φ e =
      QPower F v (-2 * (e : ℝ) / 3) •
        bCoordinate F ζ hζ v inducingData P (uniformizerUnit F v π hπ) φ (-(e : ℤ))) ∧
    ∀ (χκ : MulChar (IsLocalRing.ResidueField (valuation (LocalField F v)).integer) ℂ)
    (hactual : ∀ u, unitCharacter χκ u = arithmeticUnitCharacter F ζ hζ v hgood u)
    (l : ℤ) (hl : 1 ≤ l),
    shellContribution F ζ hζ v inducingData P μ ψ π hπ φ e l =
      (QPower F v (-2 * (e : ℝ) / 3) *
        QPower F v ((l : ℝ) / 3) *
          A μ χκ ψ π e l) •
        bCoordinate F ζ hζ v inducingData P (uniformizerUnit F v π hπ) φ (-(e : ℤ) + 2 * l) := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  constructor
  · exact ExteriorWhittakerValues.ActualShellRegion.ball_contribution_of_constant_value
      F ζ hζ v inducingData P μ N hN π hπ ψ φ e
      (fun x hx => spherical_ball_integrand_evaluation F ζ hζ v inducingData P ht φ hφ
        π hπ ψ hcond e x hx)
      (spherical_ball_mass_toReal F v μ hμ π hπ e)
  · intro χκ hactual l hl
    exact ExteriorWhittakerValues.ActualShellRegion.compatible_shell_contribution_of_scaled_value
      F ζ hζ v inducingData P μ N hN π hπ ψ hψcont φ χκ e l
      (fun u hu => ExteriorWhittakerValues.ActualShellRegion.spherical_shell_integrand_evaluation
        F ζ hζ v inducingData P ht hgood π hπ ψ φ hφ χκ hactual e l hl u hu)

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellIntegral

namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellOutput
open scoped NumberField Valued ValuativeRel BigOperators
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
open ActualSpherical ActualJacquet KPExteriorUnitShellIntegrals
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F)) (inducingData : CanonicalFiniteInducingData F ζ hζ v)
variable (P : Polarization inducingData.heisenberg)
variable (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]
variable (hμ : μ ((valuation (LocalField F v)).integer : Set (LocalField F v)) = 1)
variable (N : AddGroupNorm (Fiber F ζ hζ v inducingData P))
variable (hN : ∀ (c : ℂ) (b : Fiber F ζ hζ v inducingData P), N (c • b) = ‖c‖ * N b)
include hμ N hN
theorem spherical_truncated_decomposition
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (φ : Sections F ζ hζ v inducingData P) (e R : ℕ) :
    letI := CompatibleFiniteNorm.normedAddCommGroup N
    letI := CompatibleFiniteNorm.normedSpace N hN
    letI := CompatibleFiniteNorm.topology N
    truncatedIntegral F ζ hζ v inducingData P μ ψ π R
        (sphericalTranslate F ζ hζ v inducingData P π hπ φ e) =
      ballContribution F ζ hζ v inducingData P μ ψ π hπ φ e +
        ∑ l ∈ Finset.Icc 1 (R + e),
          shellContribution F ζ hζ v inducingData P μ ψ π hπ φ e (l : ℤ) := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  exact KPExteriorActualJacquetShells.spherical_partition_integral F v μ π hπ
    (jacquetIntegrand F ζ hζ v inducingData P ψ (sphericalTranslate F ζ hζ v inducingData P π hπ φ e)) e R
    (compact_integrability F ζ hζ v inducingData P μ hgood π hπ ψ hψcont hψunitary hcond
      (sphericalTranslate F ζ hζ v inducingData P π hπ φ e) R)

theorem spherical_ball_contribution
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (φ : Sections F ζ hζ v inducingData P)
    (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht) (hne : φ ≠ 0) (e : ℕ) :
    letI := CompatibleFiniteNorm.normedAddCommGroup N
    letI := CompatibleFiniteNorm.normedSpace N hN
    letI := CompatibleFiniteNorm.topology N
    ballContribution F ζ hζ v inducingData P μ ψ π hπ φ e =
      QPower F v (-2 * (e : ℝ) / 3) •
        bCoordinate F ζ hζ v inducingData P (uniformizerUnit F v π hπ) φ (-(e : ℤ)) := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  exact (ExteriorWhittakerValues.ActualShellIntegral.spherical_region_evaluation F ζ hζ v inducingData P μ hμ N hN
    ht hgood π hπ ψ hψcont hψunitary hcond φ hφ hne e).1

theorem spherical_shell_contribution
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (χκ : MulChar (IsLocalRing.ResidueField (valuation (LocalField F v)).integer) ℂ)
    (hactual : ∀ u, unitCharacter χκ u = arithmeticUnitCharacter F ζ hζ v hgood u)
    (φ : Sections F ζ hζ v inducingData P)
    (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht) (hne : φ ≠ 0)
    (e : ℕ) (l : ℤ) (hl : 1 ≤ l) :
    letI := CompatibleFiniteNorm.normedAddCommGroup N
    letI := CompatibleFiniteNorm.normedSpace N hN
    letI := CompatibleFiniteNorm.topology N
    shellContribution F ζ hζ v inducingData P μ ψ π hπ φ e l =
      (QPower F v (-2 * (e : ℝ) / 3) *
        QPower F v ((l : ℝ) / 3) *
          A μ χκ ψ π e l) •
        bCoordinate F ζ hζ v inducingData P (uniformizerUnit F v π hπ) φ (-(e : ℤ) + 2 * l) := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  exact (ExteriorWhittakerValues.ActualShellIntegral.spherical_region_evaluation F ζ hζ v inducingData P μ hμ N hN
    ht hgood π hπ ψ hψcont hψunitary hcond φ hφ hne e).2 χκ hactual l hl

theorem spherical_shell_vanishes
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (φ : Sections F ζ hζ v inducingData P)
    (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht) (hne : φ ≠ 0)
    (e : ℕ) (l : ℤ) (hl : (e : ℤ) + 1 < l) :
    letI := CompatibleFiniteNorm.normedAddCommGroup N
    letI := CompatibleFiniteNorm.normedSpace N hN
    letI := CompatibleFiniteNorm.topology N
    shellContribution F ζ hζ v inducingData P μ ψ π hπ φ e l = 0 := by
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (valuation (LocalField F v)).integer)
  obtain ⟨χκ, hχκ, _⟩ := exists_unique_arithmetic_residue_character F ζ hζ v hgood
  obtain ⟨ψbar, hbar, _⟩ := exists_unique_residue_addChar π hπ ψ hψcont hψunitary hcond
  rw [spherical_shell_contribution F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ hψcont
    hψunitary hcond χκ hχκ.2 φ hφ hne e l (by omega)]
  rw [unit_shell_integral μ hμ π hπ ψ hψcont hψunitary
    hcond χκ hχκ.1 ψbar hbar.2.2 e l (by omega)]
  simp [shellValue, show ¬ l ≤ (e : ℤ) by omega,
    show l ≠ (e : ℤ) + 1 by omega]

theorem stableJacquet_spherical_finite_sum
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (J : Sections F ζ hζ v inducingData P →ₗ[ℂ] Fiber F ζ hζ v inducingData P)
    (hJ : IsStableJacquet F ζ hζ v inducingData P μ N hN ψ π J)
    (φ : Sections F ζ hζ v inducingData P)
    (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht) (hne : φ ≠ 0) (e : ℕ) :
    letI := CompatibleFiniteNorm.normedAddCommGroup N
    letI := CompatibleFiniteNorm.normedSpace N hN
    letI := CompatibleFiniteNorm.topology N
    J (sphericalTranslate F ζ hζ v inducingData P π hπ φ e) =
      ballContribution F ζ hζ v inducingData P μ ψ π hπ φ e +
        ∑ l ∈ Finset.Icc 1 (e + 1),
          shellContribution F ζ hζ v inducingData P μ ψ π hπ φ e (l : ℤ) := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  obtain ⟨R₀, hR₀⟩ := hJ (sphericalTranslate F ζ hζ v inducingData P π hπ φ e)
  set R : ℕ := R₀ + e + 1 with hRdef
  have hRle : R₀ ≤ R := by omega
  rw [← hR₀ R hRle,
    spherical_truncated_decomposition F ζ hζ v inducingData P μ hμ N hN hgood π hπ ψ hψcont hψunitary
      hcond φ e R]
  have hsub : Finset.Icc 1 (e + 1) ⊆ Finset.Icc 1 (R + e) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hzero : ∀ x ∈ Finset.Icc 1 (R + e), x ∉ Finset.Icc 1 (e + 1) →
      shellContribution F ζ hζ v inducingData P μ ψ π hπ φ e (x : ℤ) = 0 := by
    intro x hxR hxnot
    simp only [Finset.mem_Icc] at hxR hxnot
    apply spherical_shell_vanishes F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ hψcont
      hψunitary hcond φ hφ hne e (x : ℤ)
    omega
  rw [← Finset.sum_subset hsub hzero]

theorem stableJacquet_spherical_coordinates
    [Fintype (IsLocalRing.ResidueField (valuation (LocalField F v)).integer)]
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (ψ : AddChar (LocalField F v) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (χκ : MulChar (IsLocalRing.ResidueField (valuation (LocalField F v)).integer) ℂ)
    (hactual : ∀ u, unitCharacter χκ u = arithmeticUnitCharacter F ζ hζ v hgood u)
    (ψbar : AddChar (IsLocalRing.ResidueField (valuation (LocalField F v)).integer) ℂ)
    (hbar : ∀ u : (valuation (LocalField F v)).integer,
      ψbar (IsLocalRing.residue _ u) = ψ ((π : LocalField F v)⁻¹ * (u : LocalField F v)))
    (J : Sections F ζ hζ v inducingData P →ₗ[ℂ] Fiber F ζ hζ v inducingData P)
    (hJ : IsStableJacquet F ζ hζ v inducingData P μ N hN ψ π J)
    (φ : Sections F ζ hζ v inducingData P)
    (hφ : φ ∈ SectionLine F ζ hζ v inducingData P ht) (hne : φ ≠ 0)
    (Eφ : (Fin 3 → ℂ) ≃ₗ[ℂ] Fiber F ζ hζ v inducingData P)
    (hEφ : ∀ j : ℤ, Eφ (KPThreeShell.basis j) =
      bCoordinate F ζ hζ v inducingData P (uniformizerUnit F v π hπ) φ j) (e : ℕ) :
    Eφ.symm (J (sphericalTranslate F ζ hζ v inducingData P π hπ φ e)) =
      KPThreeShell.shell (residueCardinality (LocalField F v) : ℝ)
        (g χκ ψbar 2) (g χκ ψbar 4) e := by
  letI := CompatibleFiniteNorm.normedAddCommGroup N
  letI := CompatibleFiniteNorm.normedSpace N hN
  letI := CompatibleFiniteNorm.topology N
  have hχ := (arithmetic_unit_shell_integrals F ζ hζ v hgood μ hμ
    π hπ ψ hψcont hψunitary hcond χκ hactual).1
  apply Eφ.injective
  rw [Eφ.apply_symm_apply]
  rw [stableJacquet_spherical_finite_sum F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ hψcont
    hψunitary hcond J hJ φ hφ hne e]
  rw [spherical_ball_contribution F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ hψcont
    hψunitary hcond φ hφ hne e]
  have hsum := KPExteriorActualJacquetShells.finite_shell_coordinate_identity
    (K := LocalField F v) χκ hχ ψbar e
  have hmap := congrArg Eφ hsum
  simp only [map_add, map_sum, map_smul, hEφ] at hmap
  simp only [KPExteriorUnitShellIntegrals.qPower, ← Nat.card_eq_fintype_card] at hmap
  change QPower F v (-2 * (e : ℝ) / 3) •
      bCoordinate F ζ hζ v inducingData P (uniformizerUnit F v π hπ) φ (-(e : ℤ)) +
      ∑ l ∈ Finset.Icc 1 (e + 1), shellContribution F ζ hζ v inducingData P μ ψ π hπ φ e (l : ℤ) =
      Eφ (KPThreeShell.shell (Nat.card (IsLocalRing.ResidueField
        (valuation (LocalField F v)).integer) : ℝ) (g χκ ψbar 2) (g χκ ψbar 4) e)
  rw [← hmap]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [spherical_shell_contribution F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ hψcont
    hψunitary hcond χκ hactual φ hφ hne e (l : ℤ) (by
      exact_mod_cast (Finset.mem_Icc.mp hl).1)]
  rw [unit_shell_integral μ hμ π hπ ψ hψcont hψunitary hcond
    χκ hχ ψbar hbar e (l : ℤ) (by exact_mod_cast (Finset.mem_Icc.mp hl).1)]
  rfl

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellOutput

end
