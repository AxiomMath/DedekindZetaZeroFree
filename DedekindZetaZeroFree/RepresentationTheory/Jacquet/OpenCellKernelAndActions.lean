module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.BruhatChartsAndCompactTransversal
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ClosedCellEvaluation
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.LocalCosetExpansions

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.KPJacquetOpenCellSections

open scoped NumberField NNReal Classical
open NumberField IsDedekindDomain
open KPLocalSmoothRepresentation KPJacquetClosedCellBump
open scoped Topology
open KPJacquetBruhatCharts

private theorem orbit_lc {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : SmoothRepresentation ρ) (v : V) :
    IsLocallyConstant (fun g => ρ g v) := by
  obtain ⟨J, hJ⟩ := hρ v
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{x | g⁻¹ * x ∈ J},
    J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using J.one_mem
  · intro x hx
    have he := congrArg (fun w => ρ g w) (hJ (g⁻¹ * x) hx)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using he

private theorem compact_avoids_inverse {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [T1Space K] {S : Set K} (hS : IsCompact S) :
    ∃ U : Set K, IsOpen U ∧ 0 ∈ U ∧ ∀ y ∈ U, ∀ x ∈ S, y * x ≠ 1 := by
  have hO : IsOpen {p : K × K | p.1 * p.2 ≠ 1} :=
    isClosed_singleton.isOpen_compl.preimage (continuous_fst.mul continuous_snd)
  obtain ⟨U, V, hU, hV, h0, hSV, hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : K))) hS hO
      (by rintro ⟨y, x⟩ ⟨hy, hx⟩; change y = 0 at hy; simp [hy])
  refine ⟨U, hU, h0 (Set.mem_singleton 0), ?_⟩
  intro y hy x hx
  exact hUV (show (y, x) ∈ U ×ˢ V from ⟨hy, hSV hx⟩)

private theorem lc_covariant_smooth
    {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup E] [Module ℂ E]
    (H : Subgroup G) (τ : Representation ℂ H E) (d : H →* (ℝ≥0)ˣ)
    (f : EqSections H τ d) (hf : IsLocallyConstant f.val)
    (C : Set G) (hC : IsCompact C)
    (hcover : (fun p : H × G => p.1.val * p.2) '' (Set.univ ×ˢ C) = Set.univ) :
    f ∈ SmoothInd H τ d := by
  have hO : IsOpen {p : G × G | f.val (p.1 * p.2) = f.val p.1} :=
    ((hf.comp_continuous (continuous_fst.mul continuous_snd)).prodMk
      (hf.comp_continuous continuous_fst)) {p | p.1 = p.2}
  obtain ⟨U, V, hU, hV, hCU, h1V, hUV⟩ :=
    generalized_tube_lemma hC (isCompact_singleton (x := (1 : G))) hO
      (by rintro ⟨g, l⟩ ⟨hg, hl⟩; simp_all)
  have hfix (l : G) (hl : l ∈ V) (g : G) : f.val (g * l) = f.val g := by
    obtain ⟨⟨b, c⟩, ⟨_, hc⟩, rfl⟩ := hcover ▸ Set.mem_univ g
    have he : f.val (c * l) = f.val c := hUV (show (c, l) ∈ U ×ˢ V from ⟨hCU hc, hl⟩)
    rw [mul_assoc, f.property, f.property, he]
  let J : Subgroup G := {
    carrier := {l | ∀ g, f.val (g * l) = f.val g}
    one_mem' := by intro g; simp
    mul_mem' := by intro a b ha hb g; rw [← mul_assoc, hb, ha]
    inv_mem' := by
      intro a ha g
      have he := ha (g * a⁻¹)
      simpa only [inv_mul_cancel_right] using he.symm }
  have hJo : IsOpen (J : Set G) := J.isOpen_of_mem_nhds
    (Filter.mem_of_superset (hV.mem_nhds (h1V (Set.mem_singleton 1)))
      (fun l hl => hfix l hl))
  apply (mem_smoothSubmodule _ _).mpr
  refine ⟨⟨J, hJo⟩, ?_⟩
  intro l hl
  apply Subtype.ext
  funext g
  exact hl g

theorem open_cell_section_smooth
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (τB : Representation ℂ (Borel F ζ hζ w) E)
    (hτB : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τB)
    (φ : KPJacquetStepFunction.CcLC (KPRankOneInduction.LocalField F w) E)
    (f : EqSections (Borel F ζ hζ w) τB (dB F ζ hζ w))
    (hopen : ∀ x : KPRankOneInduction.LocalField F w,
      f.val (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd x)) =
          KPJacquetStepFunction.value φ x)
    (hclosed : ∀ b : Borel F ζ hζ w, f.val b.val = 0) :
    f ∈ Induced F ζ hζ w m τB := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  let lam := inducingRepresentation F ζ hζ w τB
  have hlam : SmoothRepresentation lam :=
    inducingRepresentation_smooth F ζ hζ w m hm τB hm hτB
  have hcov (b : Borel F ζ hζ w) (g : FiniteCover F ζ hζ w) :
      f.val (b.val * g) = lam b (f.val g) := f.property b g
  have hΩ := (charts_open_and_borel_closed F ζ hζ w m hm).1
  have hΔ := (charts_open_and_borel_closed F ζ hζ w m hm).2.1
  have hchart : IsLocallyConstant (fun p : Borel F ζ hζ w ×
      KPRankOneInduction.LocalField F w => f.val (omegaMap F ζ hζ w p).val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro p
    have hb := ((orbit_lc lam hlam (KPJacquetStepFunction.value φ p.2)).comp_continuous
      continuous_fst).eventually_eq p
    have hx := (φ.val.isLocallyConstant.comp_continuous continuous_snd).eventually_eq p
    filter_upwards [hb, hx] with q hqb hqx
    change φ.val q.2 = φ.val p.2 at hqx
    change lam q.1 (KPJacquetStepFunction.value φ p.2) =
      lam p.1 (KPJacquetStepFunction.value φ p.2) at hqb
    change f.val (q.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd q.2)) = _
    rw [mul_assoc, hcov, hopen]
    change lam q.1 (φ.val q.2) = _
    rw [hqx]
    change lam q.1 (KPJacquetStepFunction.value φ p.2) = _
    rw [hqb]
    change _ = f.val (p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd p.2))
    rw [mul_assoc, hcov, hopen]
  have hlocal : IsLocallyConstant f.val := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro g
    by_cases hg : g ∈ omega F ζ hζ w
    · let q : omega F ζ hζ w := ⟨g, hg⟩
      have hc : IsLocallyConstant (fun q : omega F ζ hζ w => f.val q.val) := by
        have hh := hchart.comp_continuous
          (omegaHomeomorph F ζ hζ w m hm).symm.continuous
        have heq : (fun x : omega F ζ hζ w =>
            f.val (omegaMap F ζ hζ w ((omegaHomeomorph F ζ hζ w m hm).symm x)).val) =
            (fun x => f.val x.val) := by
          funext x
          exact congrArg (fun y : omega F ζ hζ w => f.val y.val)
            ((omegaHomeomorph F ζ hζ w m hm).apply_symm_apply x)
        simpa only [Function.comp_def, heq] using hh
      have he := hc.eventually_eq q
      rw [← hΩ.isOpenEmbedding_subtypeVal.map_nhds_eq q]
      exact he
    · have hgB : g ∈ Borel F ζ hζ w := by
        change g ∈ (Borel F ζ hζ w : Set (FiniteCover F ζ hζ w))
        rw [← omega_complement F ζ hζ w]; exact hg
      have hgΔ : g ∈ delta F ζ hζ w := by
        have hh := (charts_cover F ζ hζ w) ▸ Set.mem_univ g
        exact hh.resolve_left hg
      let q : delta F ζ hζ w := ⟨g, hgΔ⟩
      have hy0 : deltaCoordinate F ζ hζ w q = 0 :=
        (closed_cell_coordinate F ζ hζ w q).mp hgB
      obtain ⟨U, hU, h0U, havoid⟩ := compact_avoids_inverse φ.property
      have hy : Continuous (deltaCoordinate F ζ hζ w) :=
        (continuous_snd.comp (deltaHomeomorph F ζ hζ w m hm).symm.continuous)
      have he : ∀ᶠ r : delta F ζ hζ w in nhds q,
          deltaCoordinate F ζ hζ w r ∈ U :=
        hy.continuousAt.preimage_mem_nhds (hy0 ▸ hU.mem_nhds h0U)
      have heq : ∀ᶠ r : delta F ζ hζ w in nhds q, f.val r.val = f.val g := by
        filter_upwards [he] with r hr
        have hg0 : f.val g = 0 := hclosed ⟨g, hgB⟩
        rw [hg0]
        by_cases hrΩ : r.val ∈ omega F ζ hζ w
        · let s : omega F ζ hζ w := ⟨r.val, hrΩ⟩
          let p := (omegaHomeomorph F ζ hζ w m hm).symm s
          have hp : (omegaMap F ζ hζ w p).val = r.val :=
            congrArg Subtype.val ((omegaHomeomorph F ζ hζ w m hm).apply_symm_apply s)
          have hpx : p.2 = (deltaCoordinate F ζ hζ w r)⁻¹ :=
            (overlap_coordinates F ζ hζ w r.val hrΩ r.property).1
          have hxS : p.2 ∉ tsupport (φ.val : KPRankOneInduction.LocalField F w → E) := by
            intro hxS
            have hn := havoid _ hr _ hxS
            rw [hpx, mul_inv_cancel₀
              (overlap_coordinates F ζ hζ w r.val hrΩ r.property).2.2] at hn
            exact hn rfl
          rw [← hp]
          change f.val (p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
            upperRoot F ζ hζ w (Multiplicative.ofAdd p.2)) = 0
          rw [mul_assoc, hcov, hopen]
          change lam p.1 (φ.val p.2) = 0
          rw [image_eq_zero_of_notMem_tsupport hxS, map_zero]
        · have hrB : r.val ∈ Borel F ζ hζ w := by
            change r.val ∈ (Borel F ζ hζ w : Set (FiniteCover F ζ hζ w))
            rw [← omega_complement F ζ hζ w]; exact hrΩ
          exact hclosed ⟨r.val, hrB⟩
      rw [← hΔ.isOpenEmbedding_subtypeVal.map_nhds_eq q]
      exact heq
  exact lc_covariant_smooth _ _ _ f hlocal _
    (compactTransversal_isCompact F ζ hζ w m hm)
    (borel_mul_compactTransversal F ζ hζ w)

end DedekindZetaZeroFree.KPJacquetOpenCellSections

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPJacquetOpenCellSections

open scoped NumberField NNReal Classical
open NumberField IsDedekindDomain
open KPLocalSmoothRepresentation

theorem kernel_restriction_hasCompactSupport
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (τB : Representation ℂ (Borel F ζ hζ w) E)
    (f : Induced F ζ hζ w m τB) (hf : f.val.val 1 = 0) :
    HasCompactSupport (fun x : KPRankOneInduction.LocalField F w =>
      f.val.val (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd x))) := by
  classical
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  obtain ⟨J, hJ⟩ := (mem_smoothSubmodule _ _).mp f.property
  have hL := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).2.1
  have hn : {y : KPRankOneInduction.LocalField F w |
      lowerRoot F ζ hζ w (Multiplicative.ofAdd y) ∈ J} ∈ nhds 0 := by
    apply hL.continuousAt.preimage_mem_nhds
    have hz : KPPGLLocalCover.LowerN F ζ hζ (Sum.inr w) 0 = 1 :=
      (lowerRoot F ζ hζ w).map_one
    rw [hz]
    exact J.isOpen.mem_nhds J.one_mem
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hn
  have hzero : ∀ y : KPRankOneInduction.LocalField F w, ‖y‖ < ε →
      f.val.val (lowerRoot F ζ hζ w (Multiplicative.ofAdd y)) = 0 := by
    intro y hy
    have hj := hJ _ (he (by simpa [Metric.mem_ball, dist_zero_right] using hy))
    have hv := congrArg (fun s => s.val (1 : FiniteCover F ζ hζ w)) hj
    simpa [eqSectionsRepresentation_apply, hf] using hv
  have hlarge : ∀ x : KPRankOneInduction.LocalField F w, ε⁻¹ < ‖x‖ →
      f.val.val (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd x)) = 0 := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h; simp [h] at hx; linarith [inv_pos.mpr hε]
    have hxi : ‖x⁻¹‖ < ε := by
      rw [norm_inv]
      exact (inv_lt_comm₀ (norm_pos_iff.mpr hx0) hε).mpr hx
    let g := KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd x)
    let A := KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) *
      KubotaRankTwo.n (KPRankOneInduction.LocalField F w) x
    have hA : Matrix.ProjGenLinGroup.mk A = projection F ζ hζ w g := by
      change Matrix.ProjGenLinGroup.mk (_ * _) = _
      rw [map_mul, map_mul]
      rfl
    have hd : g ∈ KPJacquetBruhatCharts.delta F ζ hζ w := by
      refine ⟨A, hA, ?_⟩
      simpa [A, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.n,
        Matrix.GeneralLinearGroup.mkOfDetNeZero] using hx0
    have hc : KPJacquetBruhatCharts.deltaCoordinate F ζ hζ w ⟨g, hd⟩ = x⁻¹ := by
      rw [KPJacquetBruhatCharts.deltaCoordinate_eq F ζ hζ w _ A hA]
      simp [A, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.n,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, one_div]
    let b := (KPJacquetBruhatCharts.deltaInverse F ζ hζ w ⟨g, hd⟩).1
    have hb : b.val * lowerRoot F ζ hζ w (Multiplicative.ofAdd x⁻¹) = g := by
      change (g * (lowerRoot F ζ hζ w (Multiplicative.ofAdd
        (KPJacquetBruhatCharts.deltaCoordinate F ζ hζ w ⟨g, hd⟩)))⁻¹) * _ = g
      rw [hc, inv_mul_cancel_right]
    change f.val.val g = 0
    rw [← hb, f.val.property]
    simp [hzero _ hxi]
  apply HasCompactSupport.intro (K := Metric.closedBall 0 ε⁻¹)
  · exact isCompact_closedBall _ _
  · intro x hx
    apply hlarge x
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx

end DedekindZetaZeroFree.KPJacquetOpenCellSections

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPJacquetOpenCellSections

open scoped NumberField NNReal Classical
open NumberField IsDedekindDomain
open KPLocalSmoothRepresentation KPJacquetClosedCellBump

private theorem ordinaryPGLMap_injective (F : Type) [Field F] [NumberField F]
    (w : HeightOneSpectrum (RingOfIntegers F)) :
    Function.Injective (ordinaryPGLMap F w) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  intro a b
  induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
      intro h
      change Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B at h
      obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
      apply (QuotientGroup.mk'_eq_mk' _).mpr
      exact ⟨KPScalarSplitCentral.scalarMatrix F (Sum.inr w) u, ⟨u, rfl⟩, hu⟩

private theorem projection_kernel_central (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : HeightOneSpectrum (RingOfIntegers F)) :
    (projection F ζ hζ w).ker ≤ Subgroup.center (FiniteCover F ζ hζ w) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  intro g hg
  have he : KPPGLLocalCover.projection F ζ hζ (Sum.inr w) g = 1 := by
    apply ordinaryPGLMap_injective F w
    exact hg
  apply KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr w)
  rw [KPPGLLocalCover.range_centralInjection_eq_ker_projection]
  exact he

private theorem projection_kernel_finite (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : HeightOneSpectrum (RingOfIntegers F)) : Finite (projection F ζ hζ w).ker := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  have hex (g : (projection F ζ hζ w).ker) :
      ∃ z, KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) z = g.val := by
    have he : KPPGLLocalCover.projection F ζ hζ (Sum.inr w) g.val = 1 := by
      apply ordinaryPGLMap_injective F w
      exact g.property
    have hr := KPPGLLocalCover.range_centralInjection_eq_ker_projection F ζ hζ (Sum.inr w)
    rw [← MonoidHom.mem_ker, ← hr] at he
    exact he
  let e : (projection F ζ hζ w).ker → rootsOfUnity 3 F := fun g => Classical.choose (hex g)
  have he (g : (projection F ζ hζ w).ker) :
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) (e g) = g.val :=
    Classical.choose_spec (hex g)
  exact Finite.of_injective e (fun a b h => Subtype.ext (by rw [← he a, ← he b, h]))

theorem torus_conjugates_upperRoot_ratio
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (h : Torus F ζ hζ w) (x : KPRankOneInduction.LocalField F w) :
    h.val * upperRoot F ζ hζ w (Multiplicative.ofAdd x) * h.val⁻¹ =
      upperRoot F ζ hζ w (Multiplicative.ofAdd
        ((KPRankOneInduction.borelRatio F w
          (KPRankOneInduction.borelProjection F w (projection F ζ hζ w)
            (torusInBorel F ζ hζ w m hm h)) : KPRankOneInduction.LocalField F w) * x)) := by
  letI := projection_kernel_finite F ζ hζ w
  have hn (y : Multiplicative (KPRankOneInduction.LocalField F w)) :
      projection F ζ hζ w (upperRoot F ζ hζ w y) =
        KPRankOneInductionRaw.ordinaryUpperRootHom F w y := by
    change Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n _ _) =
      Matrix.ProjGenLinGroup.mk (KPRankOneInductionRaw.upperRootMatrix F w _)
    rfl
  exact FiniteCentralBorel.torusLift_conjugates_root F w
    (projection F ζ hζ w) (projection_kernel_central F ζ hζ w)
    (upperRoot F ζ hζ w) hn h.val h.property
    (torusInBorel F ζ hζ w m hm h).property x

end DedekindZetaZeroFree.KPJacquetOpenCellSections

end

end

section

noncomputable section

set_option maxHeartbeats 1600000

namespace DedekindZetaZeroFree.KPJacquetOpenCell

open scoped NumberField NNReal Classical
open NumberField IsDedekindDomain
open KPLocalSmoothRepresentation KPJacquetClosedCellBump

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
  (τB : Representation ℂ (Borel F ζ hζ w) E)
  (hτB : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τB)

abbrev TestFunctions := KPJacquetStepFunction.CcLC (KPRankOneInduction.LocalField F w) E

def extensionFunction (φ : TestFunctions F w (E := E))
    (g : FiniteCover F ζ hζ w) : E :=
  if hg : g ∈ KPJacquetBruhatCharts.omega F ζ hζ w then
    let p := KPJacquetBruhatCharts.omegaInverse F ζ hζ w ⟨g, hg⟩
    inducingRepresentation F ζ hζ w τB p.1 (KPJacquetStepFunction.value φ p.2)
  else 0

omit [FiniteDimensional ℂ E] in
 theorem extension_on (φ : TestFunctions F w (E := E))
    (b : Borel F ζ hζ w) (x : KPRankOneInduction.LocalField F w) :
    extensionFunction F ζ hζ w τB φ
      (b.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd x)) =
      (Real.sqrt ((deltaB F ζ hζ w b : ℝ≥0) : ℝ) : ℂ) •
        τB b (KPJacquetStepFunction.value φ x) := by
  obtain ⟨n, hn, _⟩ := KPLocalChartTopology.deep_chart_topology F ζ hζ w
  letI := finiteCoverTopology F ζ hζ w n
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w n hn).2.2.1
  let p := KPJacquetBruhatCharts.omegaMap F ζ hζ w (b, x)
  have hi : KPJacquetBruhatCharts.omegaInverse F ζ hζ w p = (b, x) :=
    (KPJacquetBruhatCharts.omegaHomeomorph F ζ hζ w n hn).left_inv (b, x)
  change extensionFunction F ζ hζ w τB φ p.val = _
  simp only [extensionFunction, dif_pos p.property]
  rw [hi]
  change normalizedSectionRepresentation (Borel F ζ hζ w) τB (dB F ζ hζ w) b
    (KPJacquetStepFunction.value φ x) = _
  rw [normalizedSectionRepresentation_apply]
  change (↑(↑(KPRankOneInduction.halfModulus (deltaB F ζ hζ w) b) : ℝ) : ℂ) • _ = _
  rw [KPRankOneInduction.halfModulus_eq]

omit [FiniteDimensional ℂ E] in
 theorem extension_off (φ : TestFunctions F w (E := E))
    (b : Borel F ζ hζ w) :
    extensionFunction F ζ hζ w τB φ b.val = 0 := by
  have hb : b.val ∉ KPJacquetBruhatCharts.omega F ζ hζ w := by
    change b.val ∈ (KPJacquetBruhatCharts.omega F ζ hζ w)ᶜ
    rw [KPJacquetBruhatCharts.omega_complement]
    exact b.property
  simp only [extensionFunction, dif_neg hb]

theorem extensionFunction_on (φ : TestFunctions F w (E := E))
    (b : Borel F ζ hζ w) (x : KPRankOneInduction.LocalField F w) :
    extensionFunction F ζ hζ w τB φ
      (b.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd x)) =
      (Real.sqrt ((deltaB F ζ hζ w b : ℝ≥0) : ℝ) : ℂ) •
        τB b (KPJacquetStepFunction.value φ x) := by
  exact extension_on F ζ hζ w τB φ b x

include hm in
omit [FiniteDimensional ℂ E] in
 theorem extension_covariance (φ : TestFunctions F w (E := E))
    (b : Borel F ζ hζ w) (g : FiniteCover F ζ hζ w) :
    extensionFunction F ζ hζ w τB φ (b.val * g) =
      inducingRepresentation F ζ hζ w τB b (extensionFunction F ζ hζ w τB φ g) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have hon (a : Borel F ζ hζ w) (x : KPRankOneInduction.LocalField F w) :
      extensionFunction F ζ hζ w τB φ (a.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd x)) =
        inducingRepresentation F ζ hζ w τB a (KPJacquetStepFunction.value φ x) := by
    rw [extension_on]
    change _ = (↑(↑(KPRankOneInduction.halfModulus (deltaB F ζ hζ w) a) : ℝ) : ℂ) • τB a (KPJacquetStepFunction.value φ x)
    rw [KPRankOneInduction.halfModulus_eq]
  by_cases hg : g ∈ KPJacquetBruhatCharts.omega F ζ hζ w
  · let p := KPJacquetBruhatCharts.omegaInverse F ζ hζ w ⟨g, hg⟩
    have hp : (KPJacquetBruhatCharts.omegaMap F ζ hζ w p).val = g :=
      congrArg Subtype.val ((KPJacquetBruhatCharts.omegaHomeomorph F ζ hζ w m hm).right_inv ⟨g, hg⟩)
    change p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd p.2) = g at hp
    rw [← hp, hon]
    have he : b.val * (p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd p.2)) =
        (b * p.1).val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
          upperRoot F ζ hζ w (Multiplicative.ofAdd p.2) := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [he, hon, map_mul, Module.End.mul_apply]
  · have hb : g ∈ Borel F ζ hζ w :=
      (show g ∈ (Borel F ζ hζ w : Set (FiniteCover F ζ hζ w)) from
        (KPJacquetBruhatCharts.omega_complement F ζ hζ w ▸ hg))
    have hbg : b.val * g ∈ Borel F ζ hζ w := (Borel F ζ hζ w).mul_mem b.property hb
    rw [extension_off F ζ hζ w τB φ ⟨b.val * g, hbg⟩,
      extension_off F ζ hζ w τB φ ⟨g, hb⟩, map_zero]

def ext_w (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (τB : Representation ℂ (Borel F ζ hζ w) E)
    (hτB : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τB) :
    TestFunctions F w (E := E) →ₗ[ℂ] Induced F ζ hζ w m τB where
  toFun φ := ⟨⟨extensionFunction F ζ hζ w τB φ, by
    exact extension_covariance F ζ hζ w m hm τB φ⟩, by
      apply KPJacquetOpenCellSections.open_cell_section_smooth F ζ hζ w m hm τB hτB φ
      · intro x
        change extensionFunction F ζ hζ w τB φ
          (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
            upperRoot F ζ hζ w (Multiplicative.ofAdd x)) = _
        have hon := extension_on F ζ hζ w τB φ 1 x
        simpa using hon
      · intro b
        exact extension_off F ζ hζ w τB φ b⟩
  map_add' := by
    intro φ ψ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change extensionFunction F ζ hζ w τB (φ + ψ) g =
      extensionFunction F ζ hζ w τB φ g + extensionFunction F ζ hζ w τB ψ g
    unfold extensionFunction
    split
    · exact map_add _ _ _
    · simp
  map_smul' := by
    intro c φ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change extensionFunction F ζ hζ w τB (c • φ) g =
      c • extensionFunction F ζ hζ w τB φ g
    unfold extensionFunction
    split
    · exact map_smul _ _ _
    · simp

theorem ext_w_value (φ : TestFunctions F w (E := E)) (g : FiniteCover F ζ hζ w) :
    (ext_w F ζ hζ w m hm τB hτB φ).val.val g =
      extensionFunction F ζ hζ w τB φ g := by
  rfl

include hm in
omit [FiniteDimensional ℂ E] in
 theorem restriction_locallyConstant (f : LinearMap.ker (ev1 F ζ hζ w m τB)) :
    IsLocallyConstant (fun x : KPRankOneInduction.LocalField F w => f.val.val.val
      (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd x))) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have hf : IsLocallyConstant f.val.val.val :=
    SmoothInd_le_LCSections (Borel F ζ hζ w) τB (dB F ζ hζ w) f.val.property
  exact hf.comp_continuous (continuous_const.mul
    (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).1)

def restriction (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (τB : Representation ℂ (Borel F ζ hζ w) E) :
    LinearMap.ker (ev1 F ζ hζ w m τB) →ₗ[ℂ] TestFunctions F w (E := E) where
  toFun f := ⟨⟨fun x => f.val.val.val
    (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd x)), by
      exact restriction_locallyConstant F ζ hζ w m hm τB f⟩, by
        apply KPJacquetOpenCellSections.kernel_restriction_hasCompactSupport
          F ζ hζ w m hm τB f.val
        exact f.property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem ext_w_injective : Function.Injective (ext_w F ζ hζ w m hm τB hτB) := by
  intro φ ψ h
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  have hx := congrArg (fun f : Induced F ζ hζ w m τB =>
    f.val.val (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd x))) h
  rw [ext_w_value, ext_w_value] at hx
  have hφ := extensionFunction_on F ζ hζ w τB φ 1 x
  have hψ := extensionFunction_on F ζ hζ w τB ψ 1 x
  simp only [OneMemClass.coe_one, one_mul, map_one, Units.val_one,
    NNReal.coe_one, Real.sqrt_one, Complex.ofReal_one, one_smul,
    Module.End.one_apply] at hφ hψ
  rw [hφ, hψ] at hx
  exact hx

omit [FiniteDimensional ℂ E] in
 theorem extension_mem_kernel (φ : TestFunctions F w (E := E)) :
    ext_w F ζ hζ w m hm τB hτB φ ∈ LinearMap.ker (ev1 F ζ hζ w m τB) := by
  change (ext_w F ζ hζ w m hm τB hτB φ).val.val 1 = 0
  change extensionFunction F ζ hζ w τB φ 1 = 0
  exact extension_off F ζ hζ w τB φ 1

omit [FiniteDimensional ℂ E] in
 theorem restrict_extension (φ : TestFunctions F w (E := E)) :
    restriction F ζ hζ w m hm τB
      ⟨ext_w F ζ hζ w m hm τB hτB φ,
        extension_mem_kernel F ζ hζ w m hm τB hτB φ⟩ = φ := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  change extensionFunction F ζ hζ w τB φ
    (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd x)) = _
  have h := extension_on F ζ hζ w τB φ 1 x
  simpa only [OneMemClass.coe_one, one_mul, map_one, Units.val_one,
    NNReal.coe_one, Real.sqrt_one, Complex.ofReal_one, one_smul,
    Module.End.one_apply, KPJacquetStepFunction.value] using h

omit [FiniteDimensional ℂ E] in
 theorem extension_restrict (f : LinearMap.ker (ev1 F ζ hζ w m τB)) :
    ext_w F ζ hζ w m hm τB hτB (restriction F ζ hζ w m hm τB f) = f.val := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change extensionFunction F ζ hζ w τB
    (restriction F ζ hζ w m hm τB f) g = f.val.val.val g
  by_cases hg : g ∈ KPJacquetBruhatCharts.omega F ζ hζ w
  · let p := KPJacquetBruhatCharts.omegaInverse F ζ hζ w ⟨g, hg⟩
    have hp : (KPJacquetBruhatCharts.omegaMap F ζ hζ w p).val = g :=
      congrArg Subtype.val ((KPJacquetBruhatCharts.omegaHomeomorph F ζ hζ w m hm).right_inv ⟨g, hg⟩)
    change p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd p.2) = g at hp
    rw [← hp, extension_on]
    change _ • τB p.1 (f.val.val.val _) = _
    have hf := f.val.val.property p.1
      (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        upperRoot F ζ hζ w (Multiplicative.ofAdd p.2))
    rw [normalizedSectionRepresentation_apply] at hf
    change f.val.val.val (p.1.val * _) =
      (↑(↑(KPRankOneInduction.halfModulus (deltaB F ζ hζ w) p.1) : ℝ) : ℂ) • _ at hf
    rw [KPRankOneInduction.halfModulus_eq] at hf
    simpa only [mul_assoc] using hf.symm
  · have hb : g ∈ Borel F ζ hζ w := by
      exact (show g ∈ (Borel F ζ hζ w : Set (FiniteCover F ζ hζ w)) from
        (KPJacquetBruhatCharts.omega_complement F ζ hζ w ▸ hg))
    rw [extension_off F ζ hζ w τB _ ⟨g, hb⟩]
    have hf := f.val.val.property ⟨g, hb⟩ 1
    have hzero : f.val.val.val 1 = 0 := f.property
    simpa only [mul_one, hzero, map_zero] using hf.symm

theorem range_ext_w : LinearMap.range (ext_w F ζ hζ w m hm τB hτB) =
    LinearMap.ker (ev1 F ζ hζ w m τB) := by
  apply le_antisymm
  · rintro f ⟨φ, rfl⟩
    exact extension_mem_kernel F ζ hζ w m hm τB hτB φ
  · intro f hf
    exact ⟨restriction F ζ hζ w m hm τB ⟨f, hf⟩,
      extension_restrict F ζ hζ w m hm τB hτB ⟨f, hf⟩⟩

omit [FiniteDimensional ℂ E] in
 theorem borel_stable (b : Borel F ζ hζ w) :
    LinearMap.ker (ev1 F ζ hζ w m τB) ≤
      (LinearMap.ker (ev1 F ζ hζ w m τB)).comap
        (inducedRepresentation F ζ hζ w m hm τB b.val) := by
  intro f hf
  change ev1 F ζ hζ w m τB
    (inducedRepresentation F ζ hζ w m hm τB b.val f) = 0
  rw [ev1_borel F ζ hζ w m hm τB b f]
  change ev1 F ζ hζ w m τB f = 0 at hf
  rw [hf, map_zero]

omit [FiniteDimensional ℂ E] in
def openCellRepresentation : Representation ℂ (Borel F ζ hζ w)
    (TestFunctions F w (E := E)) where
  toFun b := {
    toFun φ := restriction F ζ hζ w m hm τB
      ⟨inducedRepresentation F ζ hζ w m hm τB b.val
        (ext_w F ζ hζ w m hm τB hτB φ),
        borel_stable F ζ hζ w m hm τB b
          (extension_mem_kernel F ζ hζ w m hm τB hτB φ)⟩
    map_add' := by
      intro φ ψ
      have h : (⟨inducedRepresentation F ζ hζ w m hm τB b.val
          (ext_w F ζ hζ w m hm τB hτB (φ + ψ)),
          borel_stable F ζ hζ w m hm τB b
            (extension_mem_kernel F ζ hζ w m hm τB hτB (φ + ψ))⟩ :
          LinearMap.ker (ev1 F ζ hζ w m τB)) =
          ⟨inducedRepresentation F ζ hζ w m hm τB b.val
            (ext_w F ζ hζ w m hm τB hτB φ),
            borel_stable F ζ hζ w m hm τB b
              (extension_mem_kernel F ζ hζ w m hm τB hτB φ)⟩ +
          ⟨inducedRepresentation F ζ hζ w m hm τB b.val
            (ext_w F ζ hζ w m hm τB hτB ψ),
            borel_stable F ζ hζ w m hm τB b
              (extension_mem_kernel F ζ hζ w m hm τB hτB ψ)⟩ := by
        apply Subtype.ext
        simp only [map_add, Submodule.coe_add]
      rw [h, map_add]
    map_smul' := by
      intro c φ
      have h : (⟨inducedRepresentation F ζ hζ w m hm τB b.val
          (ext_w F ζ hζ w m hm τB hτB (c • φ)),
          borel_stable F ζ hζ w m hm τB b
            (extension_mem_kernel F ζ hζ w m hm τB hτB (c • φ))⟩ :
          LinearMap.ker (ev1 F ζ hζ w m τB)) =
          c • ⟨inducedRepresentation F ζ hζ w m hm τB b.val
            (ext_w F ζ hζ w m hm τB hτB φ),
            borel_stable F ζ hζ w m hm τB b
              (extension_mem_kernel F ζ hζ w m hm τB hτB φ)⟩ := by
        apply Subtype.ext
        simp only [map_smul, Submodule.coe_smul]
      rw [h, map_smul]
      rfl }
  map_one' := by
    apply LinearMap.ext
    intro φ
    change restriction F ζ hζ w m hm τB ⟨_, _⟩ = φ
    simp only [OneMemClass.coe_one, map_one, Module.End.one_apply]
    exact restrict_extension F ζ hζ w m hm τB hτB φ
  map_mul' := by
    intro a b
    apply LinearMap.ext
    intro φ
    change restriction F ζ hζ w m hm τB ⟨_, _⟩ =
      restriction F ζ hζ w m hm τB ⟨_, _⟩
    congr 1
    apply Subtype.ext
    change inducedRepresentation F ζ hζ w m hm τB (a * b).val
      (ext_w F ζ hζ w m hm τB hτB φ) =
      inducedRepresentation F ζ hζ w m hm τB a.val
        (ext_w F ζ hζ w m hm τB hτB
          (restriction F ζ hζ w m hm τB ⟨_, _⟩))
    rw [extension_restrict]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]

theorem ext_w_borel (b : Borel F ζ hζ w) (φ : TestFunctions F w (E := E)) :
    ext_w F ζ hζ w m hm τB hτB
      (openCellRepresentation F ζ hζ w m hm τB hτB b φ) =
      inducedRepresentation F ζ hζ w m hm τB b.val
        (ext_w F ζ hζ w m hm τB hτB φ) := by
  exact extension_restrict F ζ hζ w m hm τB hτB _

include hτB in
private theorem smooth_borel_induced :
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation (G := Borel F ζ hζ w) (V := Induced F ζ hζ w m τB)
      ((inducedRepresentation F ζ hζ w m hm τB).comp
      (Borel F ζ hζ w).subtype) := by
  letI := finiteCoverTopology F ζ hζ w m
  intro f
  obtain ⟨J, hJ⟩ := (ev1_smooth_borel F ζ hζ w m hm τB hτB).1 f
  refine ⟨J.comap (Borel F ζ hζ w).subtype continuous_subtype_val, ?_⟩
  intro b hb
  exact hJ b.val hb

private theorem smooth_open_cell :
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation (openCellRepresentation F ζ hζ w m hm τB hτB) := by
  letI := finiteCoverTopology F ζ hζ w m
  intro φ
  obtain ⟨J, hJ⟩ := smooth_borel_induced F ζ hζ w m hm τB hτB
    (ext_w F ζ hζ w m hm τB hτB φ)
  refine ⟨J, ?_⟩
  intro b hb
  apply ext_w_injective F ζ hζ w m hm τB hτB
  rw [ext_w_borel]
  exact hJ b hb

def r : Torus F ζ hζ w →* (KPRankOneInduction.LocalField F w)ˣ := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  exact {
    toFun h := KPRankOneInduction.borelRatio F w
      (KPRankOneInduction.borelProjection F w (projection F ζ hζ w)
        (torusInBorel F ζ hζ w m hm h))
    map_one' := by
      change KPRankOneInduction.borelRatio F w
        (KPRankOneInduction.borelProjection F w (projection F ζ hζ w) 1) = 1
      simp only [map_one]
    map_mul' := by
      intro a b
      change KPRankOneInduction.borelRatio F w
        (KPRankOneInduction.borelProjection F w (projection F ζ hζ w)
          (torusInBorel F ζ hζ w m hm a * torusInBorel F ζ hζ w m hm b)) = _
      simp only [map_mul] }

def d (h : Torus F ζ hζ w) : ℝ :=
  ((deltaB F ζ hζ w (torusInBorel F ζ hζ w m hm h) : ℝ≥0) : ℝ)

 theorem weyl_matrix_inv :
    (KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w))⁻¹ =
      KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.mkOfDetNeZero]

 theorem projection_weyl : projection F ζ hζ w
    (KPPGLLocalCover.W F ζ hζ (Sum.inr w)) =
      Matrix.ProjGenLinGroup.mk
        (KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w)) := rfl

def alpha : Torus F ζ hζ w →* Torus F ζ hζ w where
  toFun h := ⟨KPPGLLocalCover.W F ζ hζ (Sum.inr w) * h.val *
    (KPPGLLocalCover.W F ζ hζ (Sum.inr w))⁻¹, by
      obtain ⟨A, hA, hc, hb⟩ := h.property
      let W := KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w)
      refine ⟨W * A * W⁻¹, ?_, ?_, ?_⟩
      · rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
          projection_weyl, hA]
      · dsimp [W]
        rw [weyl_matrix_inv]
        simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
          KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.mkOfDetNeZero, hb, Matrix.vecMul, dotProduct]
      · dsimp [W]
        rw [weyl_matrix_inv]
        simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
          KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.mkOfDetNeZero, hc, Matrix.vecMul, dotProduct]⟩
  map_one' := by
    apply Subtype.ext
    change KPPGLLocalCover.W F ζ hζ (Sum.inr w) * 1 *
      (KPPGLLocalCover.W F ζ hζ (Sum.inr w))⁻¹ = 1
    simp
  map_mul' := by
    intro a b
    apply Subtype.ext
    change _ * (a.val * b.val) * _ = (_ * a.val * _) * (_ * b.val * _)
    group

def tauW : Representation ℂ (Torus F ζ hζ w) E where
  toFun h := τB (torusInBorel F ζ hζ w m hm (alpha F ζ hζ w h))
  map_one' := by
    rw [map_one]
    change τB 1 = 1
    exact map_one τB
  map_mul' := by
    intro a b
    rw [map_mul]
    change τB (torusInBorel F ζ hζ w m hm (alpha F ζ hζ w a) *
      torusInBorel F ζ hζ w m hm (alpha F ζ hζ w b)) = _
    exact map_mul τB _ _

theorem torus_conjugates_root (h : Torus F ζ hζ w)
    (x : KPRankOneInduction.LocalField F w) :
    h.val * upperRoot F ζ hζ w (Multiplicative.ofAdd x) * h.val⁻¹ =
      upperRoot F ζ hζ w (Multiplicative.ofAdd
        ((r F ζ hζ w m hm h : KPRankOneInduction.LocalField F w) * x)) := by
  exact KPJacquetOpenCellSections.torus_conjugates_upperRoot_ratio F ζ hζ w m hm h x

theorem d_eq_abs_r (h : Torus F ζ hζ w) :
    d F ζ hζ w m hm h =
      ((KPRankOneInduction.localAbs F w (r F ζ hζ w m hm h) : ℝ≥0) : ℝ) := by
  rfl

theorem d_alpha (h : Torus F ζ hζ w) :
    d F ζ hζ w m hm (alpha F ζ hζ w h) = (d F ζ hζ w m hm h)⁻¹ := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  obtain ⟨A, hA, hc, hb⟩ := h.property
  let W := KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w)
  have hWA : Matrix.ProjGenLinGroup.mk (W * A * W⁻¹) =
      projection F ζ hζ w (alpha F ζ hζ w h).val := by
    change _ = projection F ζ hζ w (_ * h.val * _)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, projection_weyl, hA]
  have hu : (W * A * W⁻¹ : KPRankOneInduction.GL2 F w) 1 0 = 0 := by
    dsimp [W]
    rw [weyl_matrix_inv]
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.mkOfDetNeZero, hb]
  change ((deltaB F ζ hζ w (torusInBorel F ζ hζ w m hm (alpha F ζ hζ w h)) : ℝ≥0) : ℝ) = _
  rw [KPRankOneInduction.deltaB_eq F w (projection F ζ hζ w) _ (W * A * W⁻¹) hWA hu]
  change _ = (((deltaB F ζ hζ w (torusInBorel F ζ hζ w m hm h) : ℝ≥0) : ℝ))⁻¹
  rw [KPRankOneInduction.deltaB_eq F w (projection F ζ hζ w) _ A hA hc]
  dsimp [W]
  rw [weyl_matrix_inv]
  have h00 : (KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) * A *
      KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w)) 0 0 = A 1 1 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h11 : (KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) * A *
      KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w)) 1 1 = A 0 0 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  change ‖(KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) * A *
    KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w)) 0 0 /
    (KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) * A *
    KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w)) 1 1‖ = _
  rw [h00, h11, ← inv_div, norm_inv]

theorem upperRoot_action
    (hτN : ∀ y, τB (rootInBorel F ζ hζ w y) = 1)
    (y x : KPRankOneInduction.LocalField F w) (φ : TestFunctions F w (E := E)) :
    KPJacquetStepFunction.value
      (openCellRepresentation F ζ hζ w m hm τB hτB
        (rootInBorel F ζ hζ w (Multiplicative.ofAdd y)) φ) x =
      KPJacquetStepFunction.value φ (x + y) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have h := congrArg (fun f : Induced F ζ hζ w m τB =>
    f.val.val (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd x)))
    (ext_w_borel F ζ hζ w m hm τB hτB
      (rootInBorel F ζ hζ w (Multiplicative.ofAdd y)) φ)
  have heval (ψ : TestFunctions F w (E := E)) :
      (ext_w F ζ hζ w m hm τB hτB ψ).val.val
        (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
          upperRoot F ζ hζ w (Multiplicative.ofAdd x)) = KPJacquetStepFunction.value ψ x := by
    rw [ext_w_value]
    simpa only [OneMemClass.coe_one, one_mul, map_one, Units.val_one,
      NNReal.coe_one, Real.sqrt_one, Complex.ofReal_one, one_smul,
      Module.End.one_apply] using extensionFunction_on F ζ hζ w τB ψ 1 x
  rw [heval] at h
  rw [h]
  change (ext_w F ζ hζ w m hm τB hτB φ).val.val
    ((KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd x)) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd y)) = _
  rw [mul_assoc, ← map_mul]
  change (ext_w F ζ hζ w m hm τB hτB φ).val.val
    (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd (x + y))) = _
  rw [ext_w_value]
  simpa only [OneMemClass.coe_one, one_mul, map_one, Units.val_one,
    NNReal.coe_one, Real.sqrt_one, Complex.ofReal_one, one_smul,
    Module.End.one_apply] using extensionFunction_on F ζ hζ w τB φ 1 (x + y)

theorem torus_action (h : Torus F ζ hζ w)
    (x : KPRankOneInduction.LocalField F w) (φ : TestFunctions F w (E := E)) :
    KPJacquetStepFunction.value
      (openCellRepresentation F ζ hζ w m hm τB hτB
        (torusInBorel F ζ hζ w m hm h) φ) x =
      ((Real.sqrt (d F ζ hζ w m hm h))⁻¹ : ℂ) •
        tauW F ζ hζ w m hm τB h
          (KPJacquetStepFunction.value φ
            (((r F ζ hζ w m hm h)⁻¹ : (KPRankOneInduction.LocalField F w)ˣ) * x)) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  let z : KPRankOneInduction.LocalField F w :=
    (((r F ζ hζ w m hm h)⁻¹ : (KPRankOneInduction.LocalField F w)ˣ) * x)
  have hz : (r F ζ hζ w m hm h : KPRankOneInduction.LocalField F w) * z = x := by
    dsimp [z]
    simp only [Units.val_inv_eq_inv_val]
    rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  have hc := torus_conjugates_root F ζ hζ w m hm h z
  rw [hz] at hc
  have hn : upperRoot F ζ hζ w (Multiplicative.ofAdd x) * h.val =
      h.val * upperRoot F ζ hζ w (Multiplicative.ofAdd z) := by
    rw [← hc]
    group
  have hw : KPPGLLocalCover.W F ζ hζ (Sum.inr w) * h.val =
      (alpha F ζ hζ w h).val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) := by
    change _ = (_ * h.val * _) * _
    group
  have hh := congrArg (fun f : Induced F ζ hζ w m τB =>
    f.val.val (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd x)))
    (ext_w_borel F ζ hζ w m hm τB hτB (torusInBorel F ζ hζ w m hm h) φ)
  have heval (ψ : TestFunctions F w (E := E)) :
      (ext_w F ζ hζ w m hm τB hτB ψ).val.val
        (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
          upperRoot F ζ hζ w (Multiplicative.ofAdd x)) = KPJacquetStepFunction.value ψ x := by
    rw [ext_w_value]
    simpa only [OneMemClass.coe_one, one_mul, map_one, Units.val_one,
      NNReal.coe_one, Real.sqrt_one, Complex.ofReal_one, one_smul,
      Module.End.one_apply] using extensionFunction_on F ζ hζ w τB ψ 1 x
  rw [heval] at hh
  rw [hh]
  change (ext_w F ζ hζ w m hm τB hτB φ).val.val
    ((KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd x)) * h.val) = _
  rw [mul_assoc, hn, ← mul_assoc, hw, ext_w_value]
  change extensionFunction F ζ hζ w τB φ
    ((torusInBorel F ζ hζ w m hm (alpha F ζ hζ w h)).val *
      KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd z)) = _
  rw [extensionFunction_on F ζ hζ w τB φ
    (torusInBorel F ζ hζ w m hm (alpha F ζ hζ w h)) z]
  change (Real.sqrt (d F ζ hζ w m hm (alpha F ζ hζ w h)) : ℂ) •
    tauW F ζ hζ w m hm τB h (KPJacquetStepFunction.value φ z) = _
  rw [d_alpha, Real.sqrt_inv, Complex.ofReal_inv]

theorem smooth_borel_short_exact :
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation (openCellRepresentation F ζ hζ w m hm τB hτB) ∧
    SmoothRepresentation (G := Borel F ζ hζ w)
      (V := Induced F ζ hζ w m τB)
      ((inducedRepresentation F ζ hζ w m hm τB).comp
        (Borel F ζ hζ w).subtype) ∧
    SmoothRepresentation (inducingRepresentation F ζ hζ w τB) ∧
    (∀ b φ, ext_w F ζ hζ w m hm τB hτB
      (openCellRepresentation F ζ hζ w m hm τB hτB b φ) =
      inducedRepresentation F ζ hζ w m hm τB b.val
        (ext_w F ζ hζ w m hm τB hτB φ)) ∧
    (∀ b f, ev1 F ζ hζ w m τB
      (inducedRepresentation F ζ hζ w m hm τB b.val f) =
      inducingRepresentation F ζ hζ w τB b (ev1 F ζ hζ w m τB f)) ∧
    Function.Injective (ext_w F ζ hζ w m hm τB hτB) ∧
    LinearMap.range (ext_w F ζ hζ w m hm τB hτB) =
      LinearMap.ker (ev1 F ζ hζ w m τB) ∧
    Function.Surjective (ev1 F ζ hζ w m τB) := by
  letI := finiteCoverTopology F ζ hζ w m
  exact ⟨smooth_open_cell F ζ hζ w m hm τB hτB,
    smooth_borel_induced F ζ hζ w m hm τB hτB,
    (ev1_smooth_borel F ζ hζ w m hm τB hτB).2,
    ext_w_borel F ζ hζ w m hm τB hτB,
    ev1_borel F ζ hζ w m hm τB,
    ext_w_injective F ζ hζ w m hm τB hτB,
    range_ext_w F ζ hζ w m hm τB hτB,
    ev1_surjective F ζ hζ w m hm τB hm hτB⟩

section TorusInflation

variable (q : Borel F ζ hζ w →* Torus F ζ hζ w)
  (τ : Representation ℂ (Torus F ζ hζ w) E)

theorem tauW_inflation
    (hqH : ∀ h, q (torusInBorel F ζ hζ w m hm h) = h)
    (h : Torus F ζ hζ w) :
    tauW F ζ hζ w m hm (inflatedRepresentation F ζ hζ w q τ) h =
      τ (alpha F ζ hζ w h) := by
  change τ (q (torusInBorel F ζ hζ w m hm (alpha F ζ hζ w h))) = _
  rw [hqH]

end TorusInflation

end DedekindZetaZeroFree.KPJacquetOpenCell

end

end
