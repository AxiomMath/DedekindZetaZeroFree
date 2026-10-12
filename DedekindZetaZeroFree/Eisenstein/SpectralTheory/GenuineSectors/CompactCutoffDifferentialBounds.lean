module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorMultiplier

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentCountableShrinking KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualCotangentPieceHilbertSum
open KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem continuous_labeledA_self :
    Continuous (labeledA (placeEquiv F ζ hζ) : M F → KPCuspGenuineMonodromy.SymmetricSpace F) := by
  apply continuous_pi
  intro k
  exact (continuous_apply (placeEquiv F ζ hζ |>.symm k)).comp
    (CotangentLogCoframe.A (d F)).continuous
private theorem isOpen_omega (a : ActualChart (U := U) (H := H)) : IsOpen (omega a) :=
  a.domain_open.preimage continuous_labeledA_self
private theorem continuous_q (a : ActualChart (U := U) (H := H)) : Continuous (q a) := by
  have hp : Continuous (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)) :=
    continuous_quotient_mk'
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative a.component)) := by
    have hh := (H.atlas U).components.continuous.comp (continuous_sigmaMk (i := a.component))
    simpa only [Function.comp_def, (H.atlas U).components_formula] using hh
  exact hc.comp (hp.comp continuous_labeledA_self)
private lemma q_coordinates (a : ActualChart (U := U) (H := H)) (y : a.domain) :
    q a (coordinates a y).val = a.toBase y := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  simp only [ShrunkChart.toBase, KPContCotangentOverlapRationalBranches.q, coordinates]
  rw [hi]
 def zext (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ) : M F → ℂ :=
  fun x => if hx : x ∈ omega a then f ⟨x, hx⟩ else 0

private theorem smooth_zext {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : ContDiffOn ℝ (⊤ : ℕ∞) (zext a f) (omega a) := by
  obtain ⟨g, hg, he⟩ := hf
  refine hg.congr (f₁ := zext a f) ?_
  intro x hx
  simpa [zext, hx] using (he ⟨x, hx⟩).symm

private theorem smooth_differential {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (zext a f) x.val)) := by
  refine ⟨fun x => CotangentLogCoframe.j (d F)
    (HyperbolicChart.differential (d F) (zext a f) x), ?_, fun _ => rfl⟩
  rw [contDiffOn_piLp]
  rintro ⟨i, k⟩
  have hd := (smooth_zext hf).fderiv_of_isOpen (isOpen_omega a) (m := (⊤ : ℕ∞)) (by simp)
  have hcd (k : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (HyperbolicChart.coordinateDerivative (d F) i k (zext a f)) (omega a) :=
    hd.clm_apply contDiffOn_const
  have hexp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : M F => (Real.exp (x (i, 2)) : ℂ)) (omega a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.exp.contDiffOn)
  fin_cases k
  · simpa [CotangentLogCoframe.j, HyperbolicChart.differential] using hcd 2
  · simpa [CotangentLogCoframe.j, HyperbolicChart.differential] using hexp.mul (hcd 0)
  · simpa [CotangentLogCoframe.j, HyperbolicChart.differential] using hexp.mul (hcd 1)

private theorem differential_frame (f : M F → ℂ) (x : M F) (k : Fin (d F) × Fin 3) :
    (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) k =
      fderiv ℝ f x (CotangentLogCoframe.H (d F) x
        (EuclideanSpace.basisFun _ ℝ k)) := by
  rcases k with ⟨i, k⟩
  fin_cases k
  · have hh : CotangentLogCoframe.H (d F) x (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))) =
        HyperbolicChart.coordinateVector (d F) i 2 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
    change (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) (i, (0 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H (d F) x
        (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative]
  · have hh : CotangentLogCoframe.H (d F) x (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector (d F) i 0 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) (i, (1 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H (d F) x
        (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]
  · have hh : CotangentLogCoframe.H (d F) x (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector (d F) i 1 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) (i, (2 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H (d F) x
        (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]

private theorem differential_frame_sum (f : M F → ℂ) (x : M F) (v : V F) :
    fderiv ℝ f x (CotangentLogCoframe.H (d F) x v) =
      ∑ k, (v k : ℂ) *
        (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) k := by
  conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun _ ℝ) v]
  simp only [EuclideanSpace.basisFun_repr, map_sum, map_smul, differential_frame,
    RCLike.real_smul_eq_coe_mul]
  rfl

private theorem differential_arrow_const {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i}
    (e : Arrow a b) (c : ℂ) (f g : M F → ℂ) (x : M F) (hx : x ∈ e.domain)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (e.psi x))
    (he : (fun y => g (e.psi y)) =ᶠ[𝓝 x] c • f) :
    CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) g (e.psi x)) =
      c • KPContCotangentRealOrthogonalComplexification.operatorComplexification _ (Q e x)
        (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) := by
  have hψ : DifferentiableAt ℝ e.psi x :=
    ((smooth_metric e).1.differentiableOn (by simp) x hx).differentiableAt
      (e.isOpen_domain.mem_nhds hx)
  have hd : (fderiv ℝ g (e.psi x)).comp (fderiv ℝ e.psi x) = c • fderiv ℝ f x := by
    rw [← fderiv_comp x hg hψ]
    change fderiv ℝ (fun y => g (e.psi y)) x = _
    rw [he.fderiv_eq, fderiv_const_smul hf]
  ext k
  rw [differential_frame]
  let v := (KPContCotangentActualGenuineTwistIsotropy.q e x hx).symm
    (EuclideanSpace.basisFun _ ℝ k)
  have hh : fderiv ℝ e.psi x (CotangentLogCoframe.H (d F) x v) =
      CotangentLogCoframe.H (d F) (e.psi x) (EuclideanSpace.basisFun _ ℝ k) := by
    apply (CotangentLogCoframe.C (d F) (e.psi x)).injective
    change Q e x v = _
    change KPContCotangentActualGenuineTwistIsotropy.q e x hx v = _
    simp [v, CotangentLogCoframe.H]
  rw [← hh]
  have hdv := congrArg (fun A : M F →L[ℝ] ℂ => A (CotangentLogCoframe.H (d F) x v)) hd
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    differential_frame_sum] at hdv
  rw [hdv]
  change _ = c *
    (KPContCotangentRealOrthogonalComplexification.operatorComplexification _ (Q e x)
      (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x))) k
  rw [KPContCotangentRealOrthogonalComplexification.operatorComplexification_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have hv : v l = Q e x (EuclideanSpace.basisFun _ ℝ l) k := by
    have hi := (KPContCotangentActualGenuineTwistIsotropy.q e x hx).inner_map_map
      v (EuclideanSpace.basisFun _ ℝ l)
    have hvq : KPContCotangentActualGenuineTwistIsotropy.q e x hx v =
        EuclideanSpace.basisFun _ ℝ k := by simp [v]
    rw [hvq] at hi
    change inner ℝ (EuclideanSpace.basisFun _ ℝ k)
      (Q e x (EuclideanSpace.basisFun _ ℝ l)) =
      inner ℝ v (EuclideanSpace.basisFun _ ℝ l) at hi
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      EuclideanSpace.basisFun_apply, Pi.single_apply] using hi.symm
  rw [hv]

private theorem smooth_ofReal {a : ActualChart (U := U) (H := H)} {f : omega a → ℝ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => (f x : ℂ)) := by
  obtain ⟨g, hg, he⟩ := hf
  exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
    fun x => by dsimp; rw [he x]⟩

private theorem differentiable_zext {a : ActualChart (U := U) (H := H)}
    {f : omega a → ℂ} (hf : SmoothOnLift a f) (x : omega a) :
    DifferentiableAt ℝ (zext a f) x.val :=
  ((smooth_zext hf).differentiableOn (by simp) x.val x.property).differentiableAt
    ((isOpen_omega a).mem_nhds x.property)

private theorem la (x : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) x) = x := by
  funext k
  simp [labeledA, labeledAInv]
private theorem al (x : M F) :
    labeledAInv (placeEquiv F ζ hζ) (labeledA (placeEquiv F ζ hζ) x) = x := by
  simp [labeledA, labeledAInv]
 def coord (g : KPCuspArithmetic.PGL2 F) (x : M F) :=
  labeledAInv (placeEquiv F ζ hζ) (g • labeledA (placeEquiv F ζ hζ) x)
local notation "cmap" => coord (ζ:=ζ) (hζ:=hζ)

 theorem coord_continuous (g : KPCuspArithmetic.PGL2 F) : Continuous (coord (ζ:=ζ) (hζ:=hζ) g) := by
  apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp ((KPCuspSiegel.continuous_action F g).comp (by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous))
 theorem chart_coord (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    coordinateMap (isotropyChart a) (targetChart a b h) g = cmap g.val := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  funext x
  simp [coordinateMap, isotropyChart, targetChart, ChartKind.representative, coord]
 theorem chart_omega (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    (targetChart a b h).omega = (isotropyChart b).omega := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  rfl
 theorem omega_open (a : ShrunkChart F ζ hζ U R P H) : IsOpen (omega a) := by
  apply a.domain_open.preimage
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
 theorem omega_subset (a : ShrunkChart F ζ hζ U R P H) :
    omega a ⊆ (isotropyChart a).omega := by
  intro x hx
  exact a.closure_subset (subset_closure hx)
 def make (a b : ShrunkChart F ζ hζ U R P H) (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    ActualBranch a b := by
  let he := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U _ g
  let r := he.choose
  let u := he.choose_spec.choose
  have hu := he.choose_spec.choose_spec
  have ht : Set.MapsTo (coordinateMap (isotropyChart a) (targetChart a b h) g)
      (omega a ∩ cmap g.val ⁻¹' omega b) (isotropyChart b).omega := by
    rw [chart_coord a b h g]
    exact fun _ hx => omega_subset b hx.2
  exact {
    component_eq := h
    arrow := {
      gamma := g, root := r⁻¹, levelLift := u,
      finite_comparison := by simpa only [inv_inv] using hu
      domain := omega a ∩ cmap g.val ⁻¹' omega b
      isOpen_domain := (omega_open a).inter ((omega_open b).preimage (coord_continuous g.val))
      source := fun _ hx => omega_subset a hx.1
      target := by rw [chart_omega a b h]; exact ht }
    source_shrinking := fun _ hx => hx.1
    target_shrinking := by
      change Set.MapsTo (coordinateMap (isotropyChart a) (targetChart a b h) g)
        (omega a ∩ cmap g.val ⁻¹' omega b) (omega b)
      rw [chart_coord a b h g]
      exact fun _ hx => hx.2
    target_larger := ht }
private theorem q_coord (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component))
    (x : M F) : q b (cmap g.val x) = q a x := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i))
  simp only [coord, la]
  apply Quotient.sound
  exact ⟨g, rfl⟩

private theorem q_branch {a b : ActualChart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) : q b (e.arrow.psi x) = q a x := by
  rw [show e.arrow.psi = cmap e.arrow.gamma.val from chart_coord a b e.component_eq e.arrow.gamma]
  exact q_coord a b e.component_eq e.arrow.gamma x

private theorem cutoff_norm_branch (η : RealSmoothCutoff F ζ hζ U R P H)
    {a b : ActualChart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) (hx : x ∈ e.arrow.domain) :
    ‖cutoffDifferential η b ⟨e.arrow.psi x, e.target_shrinking hx⟩‖ =
      ‖cutoffDifferential η a ⟨x, e.source_shrinking hx⟩‖ := by
  have hu (a : ActualChart (U := U) (H := H)) : SmoothOnLift a (cutoffLift η a) :=
    smooth_ofReal (η.smooth a)
  have he : (fun y => zext b (cutoffLift η b) (e.arrow.psi y)) =ᶠ[𝓝 x]
      (1:ℂ) • zext a (cutoffLift η a) := by
    filter_upwards [e.arrow.isOpen_domain.mem_nhds hx] with y hy
    simp [zext, e.source_shrinking hy, e.target_shrinking hy,
      cutoffLift, q_branch e y]
  have hd := differential_arrow_const e.arrow 1
    (zext a (cutoffLift η a)) (zext b (cutoffLift η b)) x hx
    (differentiable_zext (hu a) ⟨x,e.source_shrinking hx⟩)
    (differentiable_zext (hu b) ⟨_,e.target_shrinking hx⟩) he
  rw [one_smul] at hd
  change ‖CotangentLogCoframe.j (d F)
    (HyperbolicChart.differential (d F) (zext b (cutoffLift η b)) (e.arrow.psi x))‖ = _
  rw [hd]
  exact (KPContCotangentRealOrthogonalComplexification.orthogonalComplexification _
    (KPContCotangentActualGenuineTwistIsotropy.q e.arrow x hx)).norm_map _

private theorem cutoff_norm_fiber (η : RealSmoothCutoff F ζ hζ U R P H)
    (a b : ActualChart (U := U) (H := H)) (x : omega a) (y : omega b)
    (hxy : q a x.val = q b y.val) :
    ‖cutoffDifferential η a x‖ = ‖cutoffDifferential η b y‖ := by
  have hc : a.component = b.component := by
    have he : (H.atlas U).components
        ⟨a.component, KPCuspSiegel.projection F _ (labeledA (placeEquiv F ζ hζ) x.val)⟩ =
      (H.atlas U).components
        ⟨b.component, KPCuspSiegel.projection F _ (labeledA (placeEquiv F ζ hζ) y.val)⟩ := by
      simpa only [(H.atlas U).components_formula, KPContCotangentOverlapRationalBranches.q] using hxy
    exact congrArg Sigma.fst ((H.atlas U).components.injective he)
  suffices he : ∃ (e : ActualBranch a b) (hx : x.val ∈ e.arrow.domain), e.arrow.psi x.val = y.val by
    obtain ⟨e,hx,he⟩ := he
    simpa [he] using (cutoff_norm_branch η e x.val hx).symm
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at hc
  subst j
  have hi : Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative i)) := by
    intro u v huv
    have he : (H.atlas U).components ⟨i,u⟩ = (H.atlas U).components ⟨i,v⟩ := by
      simpa only [(H.atlas U).components_formula] using huv
    exact eq_of_heq (Sigma.mk.inj ((H.atlas U).components.injective he)).2
  obtain ⟨g,hg⟩ := Quotient.exact (hi hxy)
  change g.val • labeledA (placeEquiv F ζ hζ) y.val = labeledA (placeEquiv F ζ hζ) x.val at hg
  let a : ActualChart (U := U) (H := H) := ⟨i,ca,oa,da,dao,dac,das,dai⟩
  let b : ActualChart (U := U) (H := H) := ⟨i,cb,ob,db,dbo,dbc,dbs,dbi⟩
  have he : cmap g.val⁻¹ x.val = y.val := by
    rw [coord, ← hg, inv_smul_smul, al]
  refine ⟨make a b rfl g⁻¹, ⟨x.property, ?_⟩, ?_⟩
  · change cmap (g⁻¹).val x.val ∈ omega b
    simpa only [Subgroup.coe_inv, he] using y.property
  · change coordinateMap (isotropyChart a) (targetChart a b rfl) g⁻¹ x.val = y.val
    rw [chart_coord, Subgroup.coe_inv, he]

private theorem cutoff_norm_continuous (η : RealSmoothCutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) : Continuous (fun x : omega a => ‖cutoffDifferential η a x‖ ^ 2) := by
  obtain ⟨g,hg,he⟩ := smooth_differential (smooth_ofReal (η.smooth a))
  have h : (fun x : omega a => cutoffDifferential η a x) = (omega a).domRestrict g := by
    funext x; exact (he x).symm
  rw [show (fun x : omega a => ‖cutoffDifferential η a x‖ ^ 2) =
    (fun x : omega a => ‖g x.val‖ ^ 2) from congrArg (fun f => fun x => ‖f x‖ ^ 2) h]
  exact hg.continuousOn.restrict.norm.pow 2

private theorem exists_chart_point (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (y : omega a), q a y.val = x := by
  obtain ⟨cov⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hx : x ∈ ⋃ n, (cov.chart n).baseDomain := by rw [cov.covers]; trivial
  obtain ⟨n,y,hy⟩ := Set.mem_iUnion.mp hx
  refine ⟨cov.chart n, coordinates (cov.chart n) y, ?_⟩
  change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative (cov.chart n).component)
    (KPCuspSiegel.projection F _ (labeledA (placeEquiv F ζ hζ)
      (labeledAInv (placeEquiv F ζ hζ) y.val))) = x
  rw [la]; exact hy

private theorem continuous_iff_isQuotientMap {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {q : X → Y} (hq : IsQuotientMap q)
    (f : Y → Z) : Continuous f ↔ Continuous (f ∘ q) := by
  refine ⟨fun h => h.comp hq.continuous, fun h => ?_⟩
  exact Continuous.mk fun s hs => by
    rw [← hq.isOpen_preimage]
    exact h.isOpen_preimage s hs
private theorem continuous_of_all_lifts (f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hf : ∀ a : ActualChart (U := U) (H := H), Continuous (fun y : omega a => f (q a y.val))) :
    Continuous f := by
  obtain ⟨cover⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
  · intro x
    have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
  · intro n
    let a := cover.chart n
    have hloc : Continuous ((fun z : a.baseDomain => f z.val) ∘ a.quotientMap) := by
      convert (hf a).comp (coordinates_continuous a) using 1
      funext y
      exact congrArg f (q_coordinates a y).symm
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_iff_isQuotientMap (cover.properties n).quotient _).mpr hloc
private theorem cutoff_continuous (η : RealSmoothCutoff F ζ hζ U R P H) : Continuous η.val := by
  apply continuous_of_all_lifts
  intro a
  obtain ⟨g,hg,he⟩ := η.smooth a
  convert hg.continuousOn.domRestrict using 1
  exact funext (fun y => (he y).symm)
private theorem cutoffDifferential_zero (η : RealSmoothCutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (y : omega a)
    (hy : q a y.val ∉ tsupport η.val) : cutoffDifferential η a y = 0 := by
  have hz : η.val =ᶠ[𝓝 (q a y.val)] 0 := by
    filter_upwards [(isClosed_tsupport η.val).isOpen_compl.mem_nhds hy] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  have hcomp := hz.comp_tendsto (continuous_q a).continuousAt
  have hext : liftExtension a (cutoffLift η a) =ᶠ[𝓝 y.val] 0 := by
    filter_upwards [hcomp, (isOpen_omega a).mem_nhds y.property] with x hx hmem
    have hh : η.val (q a x) = 0 := hx
    simp only [liftExtension, dite_eq_left hmem, cutoffLift, hh, Complex.ofReal_zero, Pi.zero_apply]
  ext ⟨i,k⟩
  fin_cases k <;> simp [cutoffDifferential, chartDifferential, CotangentLogCoframe.j,
    HyperbolicChart.differential, HyperbolicChart.coordinateDerivative, hext.fderiv_eq]

private theorem cutoffNorm_descends (η : RealSmoothCutoff F ζ hζ U R P H) :
    ∃ f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ, Continuous f ∧
      ∀ (a : ActualChart (U := U) (H := H)) (y : omega a),
        f (q a y.val) = ‖cutoffDifferential η a y‖ ^ 2 := by
  choose chart point hpoint using (exists_chart_point (R := R) (P := P) (H := H))
  let f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ := fun x => ‖cutoffDifferential η (chart x) (point x)‖ ^ 2
  have hf (a : ActualChart (U := U) (H := H)) (y : omega a) :
      f (q a y.val) = ‖cutoffDifferential η a y‖ ^ 2 := by
    dsimp only [f]
    rw [cutoff_norm_fiber η (chart (q a y.val)) a (point (q a y.val)) y (hpoint _)]
  refine ⟨f, ?_, hf⟩
  apply continuous_of_all_lifts
  intro a
  convert cutoff_norm_continuous η a using 1
  exact funext (hf a)

private theorem compactBounds (η : RealSmoothCutoff F ζ hζ U R P H) (hcompact : HasCompactSupport η.val) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ (∀ x, |η.val x| ≤ B) ∧
      ∀ (a : ActualChart (U := U) (H := H)) (y : omega a), ‖cutoffDifferential η a y‖ ≤ D := by
  obtain ⟨f,hf,hchart⟩ := cutoffNorm_descends η
  have hsupport : tsupport f ⊆ tsupport η.val := by
    apply closure_minimal ?_ (isClosed_tsupport η.val)
    intro x hx
    by_contra hn
    obtain ⟨a,y,hy⟩ := exists_chart_point (R := R) (P := P) (H := H) x
    have hd := cutoffDifferential_zero η a y (hy ▸ hn)
    have hz : f x = 0 := by rw [← hy, hchart,hd,norm_zero,zero_pow (by decide)]
    exact hx hz
  have hcompactf : HasCompactSupport f :=
    hcompact.of_isClosed_subset (isClosed_tsupport f) hsupport
  obtain ⟨B,hB⟩ := hcompact.isCompact.exists_bound_of_continuousOn (cutoff_continuous η).continuousOn
  obtain ⟨D,hD⟩ := hcompactf.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 0, Real.sqrt (max D 0), le_max_right _ _, Real.sqrt_nonneg _, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport η.val
    · have hh : |η.val x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x hx
      exact hh.trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx,abs_zero]
      exact le_max_right _ _
  · intro a y
    have hnonneg : 0 ≤ f (q a y.val) := by rw [hchart]; positivity
    have hs : f (q a y.val) ≤ max D 0 := by
      by_cases hx : q a y.val ∈ tsupport f
      · have hh : |f (q a y.val)| ≤ D := by simpa only [Real.norm_eq_abs] using hD _ hx
        exact (le_abs_self _).trans (hh.trans (le_max_left _ _))
      · rw [image_eq_zero_of_notMem_tsupport hx]; exact le_max_right _ _
    rw [hchart] at hs
    exact (Real.le_sqrt (norm_nonneg _) (le_max_right _ _)).mpr hs

theorem compactCutoff_bounds
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (η : KPContActualSectorTestDifferentialDescent.RealSmoothCutoff F ζ hζ U R P H)
    (hcompact : HasCompactSupport η.val) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ (∀ x, |η.val x| ≤ B) ∧
      ∀ (a : KPContActualSectorSmoothTestModules.ActualChart (U := U) (H := H))
        (y : KPContCotangentOverlapRationalBranches.omega a),
        ‖KPContActualSectorTestDifferentialDescent.cutoffDifferential η a y‖ ≤ D := by
  exact compactBounds η hcompact

end DedekindZetaZeroFree.KPContActualSectorMultiplier

end
