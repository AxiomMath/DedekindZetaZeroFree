module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.LowShellCubicUnitEigencharacters

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality KPTameValuationCoordinates

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (coordinates : ∀ ε : Sign,
    sectionSpace S.borel P ε 0 ≃ₗ[ℂ] scalarSections F ζ hζ q S P hP ε)
  (hcoordinates : ∀ ε f g, (coordinates ε f).val g = (f.val g).val 1)

theorem eventually_split_subset_open (U : Set (ActualCover F ζ hζ q))
    (hU : IsOpen U) (h1 : 1 ∈ U) :
    ∃ r : ℕ, ∀ m ≥ r, splitCongruenceSet F ζ hζ q m ⊆ U := by
  obtain ⟨d, hd, hcubes, hbasis, hcharts⟩ := KPLocalCube.deep_principal_units_and_matrix_charts F q
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q d
  have htop : KPRankOneOpenCellKernel.coverTopology F ζ hζ q = KPPGLLocalCover.finiteTopology F ζ hζ q d :=
    KPPGLLocalCover.finiteTopology_independent F ζ hζ q _ d
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q) ⟨hd, (hcharts d le_rfl).2.2⟩
  have hUc : @IsOpen _ (KPPGLLocalCover.finiteTopology F ζ hζ q d) U := by rwa [← htop]
  letI : TopologicalSpace (ActualCover F ζ hζ q) := KPPGLLocalCover.finiteTopology F ζ hζ q d
  have hq : Continuous (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) := by
    exact continuous_quotient_mk'
  have hc := (KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ q d
    ⟨hd, (hcharts d le_rfl).2.2⟩ 1).continuous
  have ho : IsOpen ((KPLocalChartTopology.translatedChart F ζ hζ q d 1) ⁻¹'
      ((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) ⁻¹' U)) :=
    (hUc.preimage hq).preimage hc
  obtain ⟨V, hV, he⟩ := isOpen_induced_iff.mp ho
  have hV1 : (1 : KPLocalCube.LocalGL2 F q) ∈ V := by
    have hone : (1 : KPLocalCube.Gamma F q d) ∈
        (KPLocalChartTopology.translatedChart F ζ hζ q d 1) ⁻¹'
          ((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) ⁻¹' U) := by
      simpa [KPLocalChartTopology.translatedChart, show KPLocalCover.sectionMap F ζ hζ (Sum.inr q) 1 = 1 from rfl] using h1
    rw [← he] at hone
    exact hone
  obtain ⟨r, hr, hrV⟩ := hbasis.mem_iff.mp (hV.mem_nhds hV1)
  refine ⟨r, ?_⟩
  intro m hm k hk
  obtain ⟨g, rfl⟩ := hk
  have hgd : g.val ∈ KPLocalCube.Gamma F q d := by
    apply Subgroup.map_mono (show KPLocalCube.integerCongruence F q m ≤ KPLocalCube.integerCongruence F q d from ?_) g.property
    intro g hg
    rw [KPLocalCube.mem_integerCongruence_iff] at hg ⊢
    exact fun i j => Ideal.pow_le_pow_right (hr.trans hm) (hg i j)
  have hgr : g.val ∈ KPLocalCube.Gamma F q r := by
    apply Subgroup.map_mono (show KPLocalCube.integerCongruence F q m ≤ KPLocalCube.integerCongruence F q r from ?_) g.property
    intro g hg
    rw [KPLocalCube.mem_integerCongruence_iff] at hg ⊢
    exact fun i j => Ideal.pow_le_pow_right hm (hg i j)
  have hv : (⟨g.val, hgd⟩ : KPLocalCube.Gamma F q d) ∈ Subtype.val ⁻¹' V := hrV hgr
  rw [he] at hv
  simpa [KPLocalChartTopology.translatedChart] using hv
private theorem support_norm_right
    (g : ActualCover F ζ hζ q)
    (k : S.iwasawa.compact.toOpenSubgroup) :
    localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (g * k)))) =
    localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g))) := by
  let b : S.borel.B :=
    (S.iwasawa.borelPart (g * k))⁻¹ * S.iwasawa.borelPart g
  have he : (b : ActualCover F ζ hζ q) =
      (S.iwasawa.compactPart (g * k) : ActualCover F ζ hζ q) *
        (k : ActualCover F ζ hζ q)⁻¹ *
        (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹ := by
    have h₁ := S.iwasawa.decomposition g
    have h₂ := S.iwasawa.decomposition (g * k)
    dsimp [b]
    conv at h₂ => lhs; lhs; rw [h₁]
    have hh := congrArg (fun z : ActualCover F ζ hζ q =>
      (S.iwasawa.borelPart (g * k) : ActualCover F ζ hζ q)⁻¹ * z *
        (k : ActualCover F ζ hζ q)⁻¹ *
        (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹) h₂
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using hh
  have hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    rw [he]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem
      (S.iwasawa.compact.toOpenSubgroup.mul_mem
        (S.iwasawa.compactPart _).property
        (S.iwasawa.compact.toOpenSubgroup.inv_mem k.property))
      (S.iwasawa.compact.toOpenSubgroup.inv_mem (S.iwasawa.compactPart _).property)
  have hn := S.iwasawa.intersection_norm b hb
  have hprod : S.iwasawa.borelPart (g * k) * b = S.iwasawa.borelPart g := by
    dsimp [b]
    group
  have ha := congrArg (fun c : S.borel.B =>
    localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract c))) hprod
  simpa only [map_mul, localAbs_mul, hn, mul_one] using ha

private theorem support_norm_left
    (c : S.borel.B) (g : ActualCover F ζ hζ q) :
    localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (c * g)))) =
    localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract c)) *
      localAbs (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g))) := by
  let b : S.borel.B :=
    (S.iwasawa.borelPart (c * g))⁻¹ * c * S.iwasawa.borelPart g
  have he : (b : ActualCover F ζ hζ q) =
      (S.iwasawa.compactPart (c * g) : ActualCover F ζ hζ q) *
        (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹ := by
    have h₁ := S.iwasawa.decomposition g
    have h₂ := S.iwasawa.decomposition (c * g)
    dsimp [b]
    conv at h₂ => lhs; rhs; rw [h₁]
    have hh := congrArg (fun z : ActualCover F ζ hζ q =>
      (S.iwasawa.borelPart (c * g) : ActualCover F ζ hζ q)⁻¹ * z *
        (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹) h₂
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using hh
  have hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    rw [he]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem
      (S.iwasawa.compactPart _).property
      (S.iwasawa.compact.toOpenSubgroup.inv_mem (S.iwasawa.compactPart _).property)
  have hn := S.iwasawa.intersection_norm b hb
  have hprod : S.iwasawa.borelPart (c * g) * b = c * S.iwasawa.borelPart g := by
    dsimp [b]
    group
  have ha := congrArg (fun d : S.borel.B =>
    localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract d))) hprod
  simpa only [map_mul, localAbs_mul, hn, mul_one] using ha

private theorem support_vector_value
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ)
    (g : ActualCover F ζ hζ q) :
    (deformedTest F ζ hζ q S P hP coordinates f s).val g =
      normPower (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
        (sourceParameter .minus s) •
        ((coordinates .minus).symm f).val g := by
  let f₀ := (coordinates .minus).symm f
  have hc := f₀.property.1 (S.iwasawa.borelPart g)
    (S.iwasawa.compactPart g : ActualCover F ζ hζ q)
  rw [← S.iwasawa.decomposition g] at hc
  change inducingAction S.borel P .minus (sourceParameter .minus s)
    (S.iwasawa.borelPart g)
    (f₀.val (S.iwasawa.compactPart g : ActualCover F ζ hζ q)) = _
  rw [hc]
  change (deltaHalf S.borel (S.iwasawa.borelPart g) *
    normPower (LocalField F q) _ (sourceParameter .minus s)) •
    ((borelAction S.borel P .minus (S.iwasawa.borelPart g)) _) =
    _ • ((deltaHalf S.borel (S.iwasawa.borelPart g) *
      normPower (LocalField F q) _ 0) • _)
  simp only [normPower, zero_mul, Complex.exp_zero, mul_one, smul_smul]
  congr 1
  ring

include hcoordinates in

private theorem support_scalar_value
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ)
    (g : ActualCover F ζ hζ q) :
    ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1 =
      normPower (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
        (sourceParameter .minus s) * f.val g := by
  rw [support_vector_value]
  change _ * (((coordinates .minus).symm f).val g).val 1 = _
  have hc := hcoordinates .minus ((coordinates .minus).symm f) g
  rw [LinearEquiv.apply_symm_apply] at hc
  rw [← hc]

theorem bruhat_support_norm_right_unit
    (a t : ActualCover F ζ hζ q) (m : ℕ)
    (hnormalW : ∀ k ∈ splitCongruenceSet F ζ hζ q m,
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m)
    (hnormalT : ∀ k, k ∈ splitCongruenceSet F ζ hζ q m ↔
      t⁻¹ * k * t ∈ splitCongruenceSet F ζ hζ q m)
    (hcompact : splitCongruenceSet F ζ hζ q m ⊆ S.iwasawa.compact.toOpenSubgroup)
    (b : S.borel.B)
    (hb : a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) * t =
      b * (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q)))
    (hbunit : localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract b)) = 1)
    (x : ActualCover F ζ hζ q) (hx : x ∈ testSupport F ζ hζ q S P a m) :
    localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (x * t)))) =
    localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart x))) := by
  obtain ⟨d, k, hk, rfl⟩ := hx
  let w := KPPGLLocalCover.W F ζ hζ (Sum.inr q)
  let k' := w⁻¹ * k * w
  have hk' : k' ∈ splitCongruenceSet F ζ hζ q m := hnormalW k hk
  let k'' := t⁻¹ * k' * t
  have hk'' : k'' ∈ splitCongruenceSet F ζ hζ q m := (hnormalT k').mp hk'
  let dk : S.iwasawa.compact.toOpenSubgroup := ⟨k', hcompact hk'⟩
  let dkt : S.iwasawa.compact.toOpenSubgroup := ⟨k'', hcompact hk''⟩
  have he : (d : ActualCover F ζ hζ q) * a * k * w = d * (a * w) * dk := by
    dsimp [dk, k']; group
  have het : ((d : ActualCover F ζ hζ q) * a * k * w) * t =
      (inBorel F ζ hζ q S P d * b : S.borel.B) * (a * w) * dkt := by
    calc
      _ = d * ((a * w) * t) * k'' := by dsimp [k'', k']; group
      _ = _ := by rw [hb]; change (d : ActualCover F ζ hζ q) * ((b : ActualCover F ζ hζ q) * (a * w)) * k'' = ((d : ActualCover F ζ hζ q) * (b : ActualCover F ζ hζ q)) * (a * w) * k''; group
  change localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart ((d * a * k * w) * t)))) = _
  rw [het, he, support_norm_right F ζ hζ q S _ dkt,
    support_norm_right F ζ hζ q S _ dk,
    support_norm_left F ζ hζ q S (inBorel F ζ hζ q S P d * b)]
  have hd := support_norm_left F ζ hζ q S (inBorel F ζ hζ q S P d) (a * w)
  change localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (d * (a * w))))) = _ at hd
  rw [hd]
  simp only [map_mul, localAbs_mul, hbunit, mul_one]

include hcoordinates in

theorem deformedTest_unit_chart_conjugation
    (a t : ActualCover F ζ hζ q) (m : ℕ)
    (hnormalW : ∀ k ∈ splitCongruenceSet F ζ hζ q m,
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m)
    (hnormalT : ∀ k, k ∈ splitCongruenceSet F ζ hζ q m ↔
      t⁻¹ * k * t ∈ splitCongruenceSet F ζ hζ q m)
    (hcompact : splitCongruenceSet F ζ hζ q m ⊆ S.iwasawa.compact.toOpenSubgroup)
    (b : BL F ζ hζ q S P)
    (hb : a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) * t =
      b * (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q)))
    (hbunit : localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (inBorel F ζ hζ q S P b))) = 1)
    (hbchi : chi F ζ hζ q S P hP .minus b = 1)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f) (s : ℂ) (x : ActualCover F ζ hζ q) :
    ((deformedTest F ζ hζ q S P hP coordinates f s).val (b * x * t)).val 1 =
      ((deformedTest F ζ hζ q S P hP coordinates f s).val x).val 1 := by
  have hscalar : ∀ x, f.val (x * t) = f.val x := by
    intro x
    simpa only [hbchi, one_mul] using
      KPTameTransposeLowShellSupport.minusTest_unit_eigen_of_chart_normalization
        F ζ hζ q S P hP a t m hnormalW hnormalT b hb f hf x
  have hright : ∀ x,
      ((deformedTest F ζ hζ q S P hP coordinates f s).val (x * t)).val 1 =
        ((deformedTest F ζ hζ q S P hP coordinates f s).val x).val 1 := by
    intro y
    rw [support_scalar_value F ζ hζ q S P hP coordinates hcoordinates,
      support_scalar_value F ζ hζ q S P hP coordinates hcoordinates, hscalar]
    by_cases hy : y ∈ testSupport F ζ hζ q S P a m
    · unfold normPower
      rw [bruhat_support_norm_right_unit F ζ hζ q S P a t m hnormalW hnormalT
        hcompact (inBorel F ζ hζ q S P b) hb hbunit y hy]
    · have hf0 : f.val y = 0 := by by_contra h; exact hy (hf.2.1 h)
      rw [hf0, mul_zero, mul_zero]
  rw [show (b : ActualCover F ζ hζ q) * x * t = b * (x * t) by group]
  rw [support_scalar_value F ζ hζ q S P hP coordinates hcoordinates,
    f.property.1, hbchi, one_mul]
  have hn := support_norm_left F ζ hζ q S (inBorel F ζ hζ q S P b) (x * t)
  change localAbs (LocalField F q)
    (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (b * (x * t))))) = _ at hn
  unfold normPower
  rw [hn, hbunit, one_mul]
  have hr := hright x
  rw [support_scalar_value F ζ hζ q S P hP coordinates hcoordinates] at hr
  exact hr
namespace CubicUnitConjugationAtoms

theorem cubeLift_mem_HL (c : (LocalField F q)ˣ) :
    (S.borel.cubeLift c : actualTorus F ζ hζ q) ∈ HL F ζ hζ q S P := by
  change S.heisenberg.π (S.borel.cubeLift c) ∈ P.L
  have hc : S.heisenberg.π (S.borel.cubeLift c) = 1 := by
    exact (show (S.borel.cubeLift c : actualTorus F ζ hζ q) ∈
      S.heisenberg.π.ker by
      rw [S.heisenberg.quotient_kernel]
      exact (S.borel.cubeLift c).property)
  rw [hc]
  exact P.L.one_mem

theorem cubeLift_minus_chiH (c : (LocalField F q)ˣ)
    (hc : localAbs (LocalField F q) c = 1) :
    chiH F ζ hζ q S P hP .minus
      ⟨S.borel.cubeLift c, cubeLift_mem_HL F ζ hζ q S P c⟩ = 1 := by
  let h : HL F ζ hζ q S P :=
    ⟨S.borel.cubeLift c, cubeLift_mem_HL F ζ hζ q S P c⟩
  have hw : (weylHL F ζ hζ q S P hP h : actualTorus F ζ hζ q) =
      S.borel.cubeLift c⁻¹ := by
    change S.borel.weyl (S.borel.cubeLift c) = _
    rw [← S.borel.weylCenter_coe]
    exact congrArg Subtype.val (S.borel.weyl_cube c)
  have hh := P.extends_center (weylHL F ζ hζ q S P hP h)
    (hw ▸ (S.borel.cubeLift c⁻¹).property)
  change chiH F ζ hζ q S P hP .minus h = 1
  rw [chiH, hh]
  have he : (⟨(weylHL F ζ hζ q S P hP h : actualTorus F ζ hζ q),
    hw ▸ (S.borel.cubeLift c⁻¹).property⟩ : S.heisenberg.C) =
      S.borel.cubeLift c⁻¹ := Subtype.ext hw
  rw [he, S.borel.exceptional_cube]
  change normPower (LocalField F q) (c⁻¹ ^ 3) (1 / 6) *
    normPower (LocalField F q) (S.borel.coordinate (S.borel.cubeLift c)) (1 / 2) = 1
  rw [S.borel.cube_coordinate]
  let absHom : (LocalField F q)ˣ →* ℝ :=
    { toFun := localAbs (LocalField F q)
      map_one' := localAbs_one _
      map_mul' := localAbs_mul _ }
  have hpow : localAbs (LocalField F q) (c ^ 3) = 1 := by
    change absHom (c ^ 3) = 1
    rw [map_pow]
    change localAbs (LocalField F q) c ^ 3 = 1
    rw [hc, one_pow]
  have hinv : localAbs (LocalField F q) (c⁻¹ ^ 3) = 1 := by
    have hmul := localAbs_mul (LocalField F q) c c⁻¹
    rw [mul_inv_cancel, localAbs_one, hc, one_mul] at hmul
    change absHom (c⁻¹ ^ 3) = 1
    rw [map_pow]
    change localAbs (LocalField F q) c⁻¹ ^ 3 = 1
    rw [← hmul, one_pow]
  have hinv' : localAbs (LocalField F q) (c ^ 3)⁻¹ = 1 := by
    simpa only [inv_pow] using hinv
  simp [normPower, hpow, hinv']

theorem cubic_diagonal_mem_BL (c : (LocalField F q)ˣ) :
    KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3) ∈ BL F ζ hζ q S P := by
  refine ⟨S.borel.torus (S.borel.cubeLift c), ?_, ?_⟩
  · change S.borel.retract (S.borel.torus (S.borel.cubeLift c)) ∈ HL F ζ hζ q S P
    rw [S.borel.retract_torus]
    exact cubeLift_mem_HL F ζ hζ q S P c
  · exact (S.torus_full _).trans (S.cube_actual c)

theorem cubic_diagonal_retractL (c : (LocalField F q)ˣ) :
    retractL F ζ hζ q S P
      ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3),
        cubic_diagonal_mem_BL F ζ hζ q S P c⟩ =
      ⟨S.borel.cubeLift c, cubeLift_mem_HL F ζ hζ q S P c⟩ := by
  apply Subtype.ext
  change S.borel.retract (inBorel F ζ hζ q S P _) = _
  rw [show inBorel F ζ hζ q S P
    ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3),
      cubic_diagonal_mem_BL F ζ hζ q S P c⟩ =
      S.borel.torus (S.borel.cubeLift c) from
        Subtype.ext ((S.torus_full _).trans (S.cube_actual c)).symm]
  exact S.borel.retract_torus _

end CubicUnitConjugationAtoms

namespace CubicUnitConjugationAtoms
set_option maxHeartbeats 1000000
theorem diagonalLift_mem_actualTorus (π : (LocalField F q)ˣ) (f' : KPTameValuationCoordinates.DiagonalValuations) :
    diagonalLift F ζ hζ q π f' ∈ actualTorus F ζ hζ q := by
  change ∃ A, Matrix.ProjGenLinGroup.mk A = KPLocalSmoothRepresentation.projection F ζ hζ q (diagonalLift F ζ hζ q π f') ∧ A 1 0 = 0 ∧ A 0 1 = 0
  refine ⟨KubotaRankTwo.d (LocalField F q) (π ^ f'.1) (π ^ f'.2), ?_, ?_, ?_⟩
  · rfl
  all_goals simp [KubotaRankTwo.d]

theorem valuation_eq_one_of_localAbs_one (c : (LocalField F q)ˣ) (hc : localAbs (LocalField F q) c = 1) :
    valuation (LocalField F q) (c : LocalField F q) = 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  have hcard : (residueCardinality (LocalField F q) : ℝ) ≠ 1 := by
    have h : 1 < Nat.card 𝓀[LocalField F q] := by
      letI := Fintype.ofFinite 𝓀[LocalField F q]
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    exact ne_of_gt (by exact_mod_cast h)
  have he : WithZero.log (e (valuation (LocalField F q) (c : LocalField F q))) = 0 := by
    have hp : 0 < (residueCardinality (LocalField F q) : ℝ) := by exact_mod_cast Nat.card_pos (α := 𝓀[LocalField F q])
    have hh := (Real.rpow_right_inj hp hcard).mp (hc.trans (Real.rpow_zero _).symm)
    exact_mod_cast hh
  apply e.injective
  rw [map_one]
  have hn : e (valuation (LocalField F q) (c : LocalField F q)) ≠ 0 := by
    simp [e, c.ne_zero]
  change e (valuation (LocalField F q) (c : LocalField F q)) = 1
  rw [← WithZero.exp_log hn, he, WithZero.exp_zero]

theorem compact_diagonal_lift (u : (KPTameCompact.O F q)ˣ) (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    ∃ g : KPTameCompact.K0 F q,
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (KPGoodCompactSplitting.kStar F ζ hζ q ht g) =
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) := by
  let g := Matrix.GeneralLinearGroup.mk'' !![(u : KPTameCompact.O F q), 0; 0, 1]
    (by simpa [Matrix.det_fin_two] using u.isUnit)
  have hg : (g : Matrix (Fin 2) (Fin 2) (KPTameCompact.O F q)) = !![(u : KPTameCompact.O F q), 0; 0, 1] := rfl
  refine ⟨g, ?_⟩
  rw [KPGoodCompactSplitting.kStar_unit_diagonal F ζ hζ q ht u 1 g (by simpa using hg)]
  congr 1
  apply congrArg (KPLocalCover.sectionMap F ζ hζ (Sum.inr q))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KPTameCompact.inclusion, KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply, hg, KubotaRankTwo.d, KPTameCompact.unitInclusion, KPHilbert.integerUnitInclusion]

theorem compact_cubic_unit_lift (c : (LocalField F q)ˣ) (hc : localAbs (LocalField F q) c = 1)
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    ∃ g : KPTameCompact.K0 F q,
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (KPGoodCompactSplitting.kStar F ζ hζ q ht g) =
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3) := by
  have hv := valuation_eq_one_of_localAbs_one F q c hc
  let o : KPTameCompact.O F q := ⟨c, hv.le⟩
  have hu : IsUnit o := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation (LocalField F q)))).mpr hv
  obtain ⟨u, hu⟩ := hu
  have he : KPTameCompact.unitInclusion F q u = c := by
    apply Units.ext
    exact congrArg Subtype.val hu
  obtain ⟨g, hg⟩ := compact_diagonal_lift F ζ hζ q (u ^ 3) ht
  refine ⟨g, hg.trans ?_⟩
  congr 1
  change (KPHilbert.integerUnitInclusion F q) (u ^ 3) = c ^ 3
  rw [map_pow]
  exact congrArg (fun z => z ^ 3) he

theorem compact_weyl_lift (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    ∃ g : KPTameCompact.K0 F q,
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (KPGoodCompactSplitting.kStar F ζ hζ q ht g) =
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) := by
  let g := Matrix.GeneralLinearGroup.mk'' (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (KPTameCompact.O F q))
    (by simp [Matrix.det_fin_two])
  have hg : (g : Matrix (Fin 2) (Fin 2) (KPTameCompact.O F q)) = !![0, 1; 1, 0] := rfl
  refine ⟨g, ?_⟩
  rw [KPGoodCompactSplitting.kStar_swap_matrix F ζ hζ q ht g hg]
  congr 1
  apply congrArg (KPLocalCover.sectionMap F ζ hζ (Sum.inr q))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KPTameCompact.inclusion, KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply, hg, KPStandardLocalRootLifts.W, KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.w]

include S in
theorem actual_cube_inverse (c : (LocalField F q)ˣ) :
    (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3))⁻¹ =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c⁻¹ ^ 3) := by
  rw [← S.cube_actual, ← S.cube_actual]
  exact ((actualTorus F ζ hζ q).subtype.comp (S.heisenberg.C.subtype.comp S.borel.cubeLift)).map_inv c |>.symm

include S in
theorem diagonal_test_base_cube_relation (π : (LocalField F q)ˣ) (f' : KPTameValuationCoordinates.DiagonalValuations)
    (c : (LocalField F q)ˣ) :
    diagonalLift F ζ hζ q π f' * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
      (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3))⁻¹ =
    KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3) *
      (diagonalLift F ζ hζ q π f' * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) := by
  have hcomm := Subgroup.mem_center_iff.mp
    (S.heisenberg.central (S.borel.cubeLift c).property)
    (⟨diagonalLift F ζ hζ q π f', diagonalLift_mem_actualTorus F ζ hζ q π f'⟩ : actualTorus F ζ hζ q)
  have hh := congrArg (fun z : actualTorus F ζ hζ q => (z : ActualCover F ζ hζ q)) hcomm
  change diagonalLift F ζ hζ q π f' * ((S.borel.cubeLift c : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) =
    ((S.borel.cubeLift c : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) * diagonalLift F ζ hζ q π f' at hh
  rw [S.cube_actual] at hh
  rw [actual_cube_inverse F ζ hζ q S c, mul_assoc,
    KPCorrectedBruhatLifts.quotient_weyl_diagonal F ζ hζ (Sum.inr q)]
  simp only [inv_pow, inv_inv] at *
  rw [← mul_assoc, hh, mul_assoc]

end CubicUnitConjugationAtoms

include hcoordinates in

theorem deep_diagonal_test_cubic_unit_conjugation
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ) (f' : DiagonalValuations) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π f') m f →
      ∀ c : (LocalField F q)ˣ, localAbs (LocalField F q) c = 1 →
      ∀ s : ℂ, ∀ g : ActualCover F ζ hζ q,
        ((deformedTest F ζ hζ q S P hP coordinates f s).val
          (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3) * g *
            (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3))⁻¹)).val 1 =
        ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1 := by
  obtain ⟨D, hD, _, _, hcharts⟩ := KPLocalCube.deep_principal_units_and_matrix_charts F q
  obtain ⟨R, hR⟩ := eventually_split_subset_open F ζ hζ q
    (S.iwasawa.compact.toOpenSubgroup : Set (ActualCover F ζ hζ q))
    S.iwasawa.compact.toOpenSubgroup.isOpen S.iwasawa.compact.toOpenSubgroup.one_mem
  refine ⟨max D R, ?_⟩
  intro m hm f hf c hc s g
  have hmd : D ≤ m := (le_max_left _ _).trans hm
  have hmr : R ≤ m := (le_max_right _ _).trans hm
  have hdepth : KPLocalChartTopology.MatrixChartDepth F q m := ⟨hD.trans hmd, (hcharts m hmd).2.2⟩
  obtain ⟨gw, hgw⟩ := CubicUnitConjugationAtoms.compact_weyl_lift F ζ hζ q htame
  have hnormalW : ∀ k ∈ splitCongruenceSet F ζ hζ q m,
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m := by
    intro k hk
    simpa only [hgw] using
      (KPTameTransposeLowShellSupport.compact_normalizes_splitCongruenceSet
        F ζ hζ q htame m hdepth gw k).mp hk
  obtain ⟨gt, hgt⟩ := CubicUnitConjugationAtoms.compact_cubic_unit_lift F ζ hζ q c hc htame
  let t := (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3))⁻¹
  have hnormalT : ∀ k, k ∈ splitCongruenceSet F ζ hζ q m ↔
      t⁻¹ * k * t ∈ splitCongruenceSet F ζ hζ q m := by
    intro k
    have he := KPTameTransposeLowShellSupport.compact_normalizes_splitCongruenceSet
      F ζ hζ q htame m hdepth gt⁻¹ k
    rw [map_inv, map_inv, hgt] at he
    exact he
  let b : BL F ζ hζ q S P := ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3),
    CubicUnitConjugationAtoms.cubic_diagonal_mem_BL F ζ hζ q S P c⟩
  have hbchi : chi F ζ hζ q S P hP .minus b = 1 := by
    rw [chi, CubicUnitConjugationAtoms.cubic_diagonal_retractL]
    exact CubicUnitConjugationAtoms.cubeLift_minus_chiH F ζ hζ q S P hP c hc
  have hbunit : localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (inBorel F ζ hζ q S P b))) = 1 := by
    change localAbs (LocalField F q) (S.borel.coordinate (retractL F ζ hζ q S P b)) = 1
    rw [CubicUnitConjugationAtoms.cubic_diagonal_retractL, S.borel.cube_coordinate]
    have h := localAbs_mul (LocalField F q)
    simp only [pow_succ, pow_zero, h, hc, localAbs_one, one_mul]
  exact deformedTest_unit_chart_conjugation F ζ hζ q S P hP coordinates hcoordinates
    (diagonalLift F ζ hζ q π f') t m hnormalW hnormalT (hR m hmr) b
    (CubicUnitConjugationAtoms.diagonal_test_base_cube_relation F ζ hζ q S π f' c)
    hbunit hbchi f hf s g

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

end
