module

public import DedekindZetaZeroFree.Adeles.Approximation.ArchimedeanChartMultiplication

public import DedekindZetaZeroFree.Metaplectic.Kubota.ArchimedeanUpperCurves

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
open _root_.DedekindZetaZeroFree.KPLiteralChamber.JointProfile.ArchChartProduct renaming product_coordinate → product_coordinate
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPGlobalResidualConstruction KPLiteralChamber
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def chartProduct (p : ArchCoordinates F × ArchCoordinates F) : ArchCoordinates F := fun q =>
  ![p.1 q 0 + p.1 q 1 * p.2 q 0 / (1 + p.1 q 2 * p.2 q 0),
    p.1 q 1 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)^2,
    p.2 q 2 + p.1 q 2 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)]

theorem chartProduct_chart (x y : ArchCoordinates F) (hx : x ∈ archDomain F)
    (hy : y ∈ archDomain F) (hden : ∀ w, 1 + x w 2 * y w 0 ≠ 0) :
    archChart F R.A.zeta12 R.A.primitive_zeta12 (chartProduct (x,y)) =
      archChart F R.A.zeta12 R.A.primitive_zeta12 x *
        archChart F R.A.zeta12 R.A.primitive_zeta12 y := by
  rw [right_insertion, right_insertion, right_insertion,
    ← (KPSmoothActualFlowData.archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).2.1]
  congr 1
  funext w
  change Matrix.ProjGenLinGroup.mk (rightMatrix (chartProduct (x,y) w)) =
    Matrix.ProjGenLinGroup.mk (rightMatrix (x w)) * Matrix.ProjGenLinGroup.mk (rightMatrix (y w))
  rw [← map_mul]
  have hc : chartProduct (x,y) w = rightCoordinates (rightMatrix (x w) * rightMatrix (y w)).val := by
    exact (product_coordinate (x w) (y w) (hx w) (hy w) (hden w)).symm
  rw [hc]
  apply rightCoordinates_reconstruct
  simpa [Units.val_mul, rightMatrix_val _ (hx w), rightMatrix_val _ (hy w),
    Matrix.mul_apply, Fin.sum_univ_two, add_comm] using hden w

def upperTransport (w : InfinitePlace F) (b : Bool) (x : ArchCoordinates F) (t : ℝ) :=
  chartProduct (x, upperCoordinates w b t)

def upperField (w : InfinitePlace F) (b : Bool) (x : ArchCoordinates F) : ArchCoordinates F :=
  fun v => if v = w then
    ![x v 1 * direction b, -2 * x v 1 * x v 2 * direction b, -(x v 2)^2 * direction b]
    else 0

theorem upperTransport_zero (w : InfinitePlace F) (b : Bool) (x : ArchCoordinates F) :
    upperTransport w b x 0 = x := by
  funext v i
  fin_cases i <;> simp [upperTransport, chartProduct, upperCoordinates]

theorem upperField_smooth (w : InfinitePlace F) (b : Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (upperField w b) := by
  apply contDiff_pi.mpr; intro v
  by_cases hv : v = w
  · apply contDiff_pi.mpr; intro i
    fin_cases i <;> simp [upperField, hv]
    all_goals fun_prop
  · simpa [upperField, hv] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : ArchCoordinates F => (0 : Fin 3 → ℂ)))

theorem upperTransport_hasDeriv (w : InfinitePlace F) (b : Bool) (x : ArchCoordinates F) :
    HasDerivAt (upperTransport w b x) (upperField w b x) 0 := by
  apply hasDerivAt_pi.mpr; intro v
  apply hasDerivAt_pi.mpr; intro i
  have ht := Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))
  have ha : HasDerivAt (fun t : ℝ => (t : ℂ) * direction b) (direction b) 0 := by
    simpa using ht.mul_const (direction b)
  have hd : HasDerivAt (fun t : ℝ => 1 + x v 2 * ((t : ℂ) * direction b))
      (x v 2 * direction b) 0 := by
    convert (hasDerivAt_const 0 (1 : ℂ)).add (ha.const_mul (x v 2)) using 1 <;> simp
  by_cases hv : v = w
  · fin_cases i
    · convert (hasDerivAt_const 0 (x v 0)).add
        ((ha.const_mul (x v 1)).div hd (by simp)) using 1
      · funext t; simp [upperTransport, chartProduct, upperCoordinates, hv]
      · simp [upperField, hv]
    · convert (hasDerivAt_const 0 (x v 1)).div (hd.pow 2) (by simp) using 1
      · funext t; simp [upperTransport, chartProduct, upperCoordinates, hv]
      · simp [upperField, hv]; ring
    · convert (hasDerivAt_const 0 (x v 2)).div hd (by simp) using 1
      · funext t; simp [upperTransport, chartProduct, upperCoordinates, hv]
      · simp [upperField, hv]; ring
  · convert hasDerivAt_const (0 : ℝ) (x v i) using 1
    · funext t; fin_cases i <;> simp [upperTransport, chartProduct, upperCoordinates, hv]
    · simp [upperField, hv]

theorem upperLieDerivative_chart (w : InfinitePlace F) (b : Bool) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f) (g : Group R)
    (x : ArchCoordinates F) (hx : x ∈ archDomain F) :
    upperLieDerivative R w b f (g * archChart F R.A.zeta12 R.A.primitive_zeta12 x) =
      fderiv ℝ (fun y => f (g * archChart F R.A.zeta12 R.A.primitive_zeta12 y)) x
        (upperField w b x) := by
  have hO : IsOpen (archDomain F) := KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F
  have hd := ((hf.2.1 g).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have ht := upperTransport_hasDeriv w b x
  have hder := (upperTransport_zero w b x).symm ▸ hd.hasFDerivAt
  have hder := hder.comp_hasDerivAt 0 ht
  rw [upperTransport_zero] at hder
  have he : (fun t => f ((g * archChart F R.A.zeta12 R.A.primitive_zeta12 x) *
      upperCurve R w b t)) =ᶠ[𝓝 (0 : ℝ)] (fun t => f (g *
      archChart F R.A.zeta12 R.A.primitive_zeta12 (upperTransport w b x t))) := by
    have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v, 1 + x v 2 * upperCoordinates w b t v 0 ≠ 0 := by
      apply eventually_all.mpr; intro v
      have hc : ContinuousAt (fun t : ℝ => 1 + x v 2 * upperCoordinates w b t v 0) 0 := by
        have hcv : Continuous (fun t : ℝ => upperCoordinates w b t v 0) :=
          (continuous_apply 0).comp ((continuous_apply v).comp
            (upperCoordinates_smooth w b).continuous)
        exact continuousAt_const.add (continuousAt_const.mul hcv.continuousAt)
      exact hc.eventually_ne (by simp [upperCoordinates])
    filter_upwards [hn] with t ht
    rw [← upperCoordinates_chart, mul_assoc, ← chartProduct_chart R x _ hx
      (by intro v; simp [upperCoordinates]) ht]
    rfl
  change deriv (fun t => f ((g * archChart F R.A.zeta12 R.A.primitive_zeta12 x) *
    upperCurve R w b t)) 0 = _
  rw [he.deriv_eq]
  exact hder.deriv

theorem upperLieDerivative_chart_smooth (w : InfinitePlace F) (b : Bool) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f) (g : Group R) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => upperLieDerivative R w b f
      (g * archChart F R.A.zeta12 R.A.primitive_zeta12 x)) (archDomain F) := by
  have hO : IsOpen (archDomain F) := KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F
  exact (((hf.2.1 g).fderiv_of_isOpen hO (by simp)).clm_apply
    (upperField_smooth w b).contDiffOn).congr
      (fun x hx => upperLieDerivative_chart R w b f hf g x hx)

theorem upperLieDerivative_level (w : InfinitePlace F) (b : Bool) (f : Functions R)
    (U : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12)
    (hU : ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U →
      f (g * u) = f g) (g u : Group R)
    (hu : u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U) :
    upperLieDerivative R w b f (g * u) = upperLieDerivative R w b f g := by
  obtain ⟨V, hVo, hb, hVD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product
      F R.A.zeta12 R.A.primitive_zeta12
  change deriv (fun t => f ((g * u) * upperCurve R w b t)) 0 =
    deriv (fun t => f (g * upperCurve R w b t)) 0
  congr 1
  funext t
  rw [← upperCoordinates_chart, mul_assoc, (hcomm U u hu _).eq.symm,
    ← mul_assoc, hU _ u hu]

theorem upperLieDerivative_smooth (w : InfinitePlace F) (b : Bool) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (upperLieDerivative R w b f) := by
  obtain ⟨U, hU⟩ := hf.2.2
  have hlevel := upperLieDerivative_level R w b f U hU
  have hchart := upperLieDerivative_chart_smooth R w b f hf
  refine ⟨?_, hchart, U, hlevel⟩
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  obtain ⟨V, hVo, hb, hVD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product
      F R.A.zeta12 R.A.primitive_zeta12
  apply continuous_iff_continuousAt.mpr
  intro g
  let q := fun x => upperLieDerivative R w b f
    (g * archChart F R.A.zeta12 R.A.primitive_zeta12 x)
  have hbase : q (archBase F) = upperLieDerivative R w b f g := by
    simp [q, KPInterface.ResidueConstruction.Raw.archChart_base]
  apply tendsto_def.mpr
  intro O hO
  have hc : ContinuousAt q (archBase F) :=
    (hchart g).continuousOn.continuousAt
      ((KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).mem_nhds (hVD hb))
  have hn : q ⁻¹' O ∈ 𝓝 (archBase F) := hc (by rwa [hbase])
  obtain ⟨W, hW, hWo, hbW⟩ := mem_nhds_iff.mp (inter_mem hn (hVo.mem_nhds hb))
  have hWV : W ⊆ V := fun x hx => (hW hx).2
  have hth := hthick W hWo hbW hWV U
  change ∀ᶠ z in 𝓝 (1 : Group R), ∃ x ∈ W, ∃ u ∈
    KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U,
    z = archChart F R.A.zeta12 R.A.primitive_zeta12 x * u at hth
  have hg : ∀ᶠ z in 𝓝 g, ∃ x ∈ W, ∃ u ∈
      KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U,
      g⁻¹ * z = archChart F R.A.zeta12 R.A.primitive_zeta12 x * u :=
    (show ContinuousAt (fun z : Group R => g⁻¹ * z) g from
      continuousAt_const.mul continuousAt_id).eventually (by simpa using hth)
  filter_upwards [hg] with z hz
  obtain ⟨x, hx, u, hu, he⟩ := hz
  have hz : z = (g * archChart F R.A.zeta12 R.A.primitive_zeta12 x) * u := by
    calc z = g * (g⁻¹ * z) := by simp
         _ = _ := by rw [he]; group
  change upperLieDerivative R w b f z ∈ O
  rw [hz, hlevel _ u hu]
  exact (hW hx).1

end DedekindZetaZeroFree.RootDerivatives

end
