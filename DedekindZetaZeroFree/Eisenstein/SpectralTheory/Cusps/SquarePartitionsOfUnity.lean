module

public import DedekindZetaZeroFree.Eisenstein.Continuation.RadialCutoffs.SmoothZeroExtension
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSquareEndPartition

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentCountableShrinking KPContCotangentOverlapRationalBranches

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Base := KPFiniteCuspAtlas.rawXU F ζ hζ U

abbrev CuspIndex := KPContActualCollarBuffer.CuspIndex F ζ hζ U R P H

def AboveEndStarts (T : ℝ) : Prop :=
  ∀ c : CuspIndex F ζ hζ U R P H, ((H.atlas U).cuspAtlas c.1).threshold < T

def differentialSupport (η : Cutoff F ζ hζ U R P H) : Set (Base F ζ hζ U) :=
  closure {x | ∃ (a : ActualChart (U := U) (H := H)) (y : omega a),
    q a y.val = x ∧ cutoffDifferential η a y ≠ 0}

section NormDescentHelpers
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContActualCotangentMeasurableFamilies KPContActualCotangentPieceHilbertSum
variable {F ζ hζ U R P H}

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

private theorem smooth_ofReal {a : ActualChart (U := U) (H := H)} {f : omega a → ℝ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => (f x : ℂ)) := by
  obtain ⟨g, hg, he⟩ := hf
  exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
    fun x => by dsimp; rw [he x]⟩

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

private theorem cutoff_norm_branch (η : Cutoff F ζ hζ U R P H)
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

private theorem cutoff_norm_fiber (η : Cutoff F ζ hζ U R P H)
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

private theorem cutoff_norm_continuous (η : Cutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) : Continuous (fun x : omega a => ‖cutoffDifferential η a x‖ ^ 2) := by
  obtain ⟨g,hg,he⟩ := smooth_differential (smooth_ofReal (η.smooth a))
  have h : (fun x : omega a => cutoffDifferential η a x) = (omega a).domRestrict g := by
    funext x; exact (he x).symm
  rw [show (fun x : omega a => ‖cutoffDifferential η a x‖ ^ 2) =
    (fun x : omega a => ‖g x.val‖ ^ 2) from congrArg (fun f => fun x => ‖f x‖ ^ 2) h]
  exact hg.continuousOn.restrict.norm.pow 2

private theorem exists_chart_point (x : Base F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (y : omega a), q a y.val = x := by
  obtain ⟨cov⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hx : x ∈ ⋃ n, (cov.chart n).baseDomain := by rw [cov.covers]; trivial
  obtain ⟨n,y,hy⟩ := Set.mem_iUnion.mp hx
  refine ⟨cov.chart n, coordinates (cov.chart n) y, ?_⟩
  change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative (cov.chart n).component)
    (KPCuspSiegel.projection F _ (labeledA (placeEquiv F ζ hζ)
      (labeledAInv (placeEquiv F ζ hζ) y.val))) = x
  rw [la]; exact hy

private theorem continuous_iff_quotient {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {q : X → Y} (hq : IsQuotientMap q)
    (f : Y → Z) : Continuous f ↔ Continuous (f ∘ q) := by
  refine ⟨fun h => h.comp hq.continuous, fun h => ?_⟩
  exact Continuous.mk fun s hs => by
    rw [← hq.isOpen_preimage]
    exact h.isOpen_preimage s hs

private theorem q_coordinates (a : ActualChart (U := U) (H := H)) (y : a.domain) :
    q a (coordinates a y).val = a.toBase y := by
  simp only [ShrunkChart.toBase, KPContCotangentOverlapRationalBranches.q, coordinates]
  rw [la]

end NormDescentHelpers

theorem differentialNormSquared_descends (η : Cutoff F ζ hζ U R P H) :
    ∃! f : Base F ζ hζ U → ℝ, Continuous f ∧
      ∀ (a : ActualChart (U := U) (H := H)) (y : omega a),
        f (q a y.val) = ‖cutoffDifferential η a y‖ ^ 2 := by
  classical
  choose chart point hpoint using (exists_chart_point (R := R) (P := P) (H := H))
  let f : Base F ζ hζ U → ℝ := fun x => ‖cutoffDifferential η (chart x) (point x)‖ ^ 2
  have hf (a : ActualChart (U := U) (H := H)) (y : omega a) :
      f (q a y.val) = ‖cutoffDifferential η a y‖ ^ 2 := by
    dsimp only [f]
    rw [cutoff_norm_fiber η (chart (q a y.val)) a (point (q a y.val)) y (hpoint _)]
  have hcont : Continuous f := by
    obtain ⟨cover⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
    refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
    · intro x
      have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
      exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
    · intro n
      let a := cover.chart n
      have hloc := (cutoff_norm_continuous η a).comp
        (KPContActualCotangentPieceHilbertSum.coordinates_continuous a)
      have he : (fun z : a.baseDomain => f z.val) ∘ a.quotientMap =
          (fun y : a.domain => ‖cutoffDifferential η a
            (KPContActualCotangentPieceHilbertSum.coordinates a y)‖ ^ 2) := by
        funext y
        change f (a.toBase y) = _
        rw [← q_coordinates a y, hf]
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_iff_quotient
        (every_shrunkChart_properties F ζ hζ U R P H a).quotient _).mpr (he ▸ hloc)
  refine ⟨f, ⟨hcont,hf⟩, ?_⟩
  intro g hg
  funext x
  obtain ⟨a,y,hy⟩ := exists_chart_point (R := R) (P := P) (H := H) x
  rw [← hy, hg.2, hf]

def differentialNormSquared (η : Cutoff F ζ hζ U R P H) : Base F ζ hζ U → ℝ :=
  Classical.choose (differentialNormSquared_descends F ζ hζ U R P H η)

theorem differentialNormSquared_chart (η : Cutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (y : omega a) :
    differentialNormSquared F ζ hζ U R P H η (q a y.val) =
      ‖cutoffDifferential η a y‖ ^ 2 := by
  exact (Classical.choose_spec (differentialNormSquared_descends F ζ hζ U R P H η)).1.2 a y

theorem differentialSupport_eq_tsupport (η : Cutoff F ζ hζ U R P H) :
    differentialSupport F ζ hζ U R P H η =
      tsupport (differentialNormSquared F ζ hζ U R P H η) := by
  obtain ⟨cov⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hcov : ∀ x : Base F ζ hζ U, ∃ n, x ∈ (cov.chart n).baseDomain := by
    intro x
    have h := cov.covers
    rw [Set.eq_univ_iff_forall] at h
    simpa [Set.mem_iUnion] using h x
  unfold differentialSupport tsupport
  congr 1
  ext x
  constructor
  · rintro ⟨a, y, rfl, hy⟩
    simp only [Function.mem_support]
    rw [differentialNormSquared_chart F ζ hζ U R P H η a y]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  · intro hx
    simp only [Function.mem_support] at hx
    obtain ⟨n, hn⟩ := hcov x
    obtain ⟨y, hy⟩ := hn
    let x' : KPContCotangentActualOverlap.M F := KPContCotangentActualOverlap.labeledAInv
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ) y.val
    have hx' : KPContCotangentActualOverlap.labeledA
        (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x' = y.val := by
      funext k
      show (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F))
          ((CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).symm
            (fun k' => y.val (KPContCotangentActualOverlap.placeEquiv F ζ hζ k')))
          ((KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm k) = y.val k
      rw [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hmem : x' ∈ KPContCotangentOverlapRationalBranches.omega (cov.chart n) := by
      show KPContCotangentActualOverlap.labeledA
        (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x' ∈ (cov.chart n).domain
      rw [hx']; exact y.property
    have hqx : KPContCotangentOverlapRationalBranches.q (cov.chart n) x' = x := by
      rw [← hy]
      unfold KPContCotangentOverlapRationalBranches.q ShrunkChart.toBase
      rw [hx']
    refine ⟨cov.chart n, ⟨x', hmem⟩, hqx, ?_⟩
    · rw [← hqx] at hx
      rw [differentialNormSquared_chart F ζ hζ U R P H η (cov.chart n) ⟨x', hmem⟩] at hx
      exact fun hz => hx (by rw [hz]; simp)

def collarError (χ₀ : Cutoff F ζ hζ U R P H)
    (χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H) : Base F ζ hζ U → ℝ :=
  fun x => differentialNormSquared F ζ hζ U R P H χ₀ x +
    ∑ c, differentialNormSquared F ζ hζ U R P H (χ c) x

theorem continuous_differentialNormSquared (η : Cutoff F ζ hζ U R P H) :
    Continuous (differentialNormSquared F ζ hζ U R P H η) :=
  (Classical.choose_spec (differentialNormSquared_descends F ζ hζ U R P H η)).1.1

theorem differentialNormSquared_nonnegative (η : Cutoff F ζ hζ U R P H) (x : Base F ζ hζ U) :
    0 ≤ differentialNormSquared F ζ hζ U R P H η x := by
  obtain ⟨cov⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hx : x ∈ ⋃ n, (cov.chart n).baseDomain := by rw [cov.covers]; trivial
  obtain ⟨n, y, hy⟩ := Set.mem_iUnion.mp hx
  let z := KPContActualCotangentPieceHilbertSum.coordinates (cov.chart n) y
  have hz : q (cov.chart n) z.val = x := by
    change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative (cov.chart n).component)
      (KPCuspSiegel.projection F _ (KPContCotangentActualOverlap.labeledA
        (KPContCotangentActualOverlap.placeEquiv F ζ hζ) z.val)) = x
    have he : KPContCotangentActualOverlap.labeledA
        (KPContCotangentActualOverlap.placeEquiv F ζ hζ) z.val = y.val := by
      funext k
      simp [z, KPContActualCotangentPieceHilbertSum.coordinates,
        KPContCotangentActualOverlap.labeledA, KPContCotangentActualOverlap.labeledAInv]
    rw [he]
    exact hy
  rw [← hz, differentialNormSquared_chart]
  exact sq_nonneg _

theorem collarError_continuous_nonnegative (χ₀ : Cutoff F ζ hζ U R P H)
    (χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H) :
    Continuous (collarError F ζ hζ U R P H χ₀ χ) ∧
      ∀ x, 0 ≤ collarError F ζ hζ U R P H χ₀ χ x := by
  refine ⟨(continuous_differentialNormSquared F ζ hζ U R P H χ₀).add
    (continuous_finset_sum _ (fun c _ => continuous_differentialNormSquared F ζ hζ U R P H (χ c))), ?_⟩
  intro x
  exact add_nonneg (differentialNormSquared_nonnegative F ζ hζ U R P H χ₀ x)
    (Finset.sum_nonneg (fun c _ => differentialNormSquared_nonnegative F ζ hζ U R P H (χ c) x))

theorem collarError_compact_bounded (χ₀ : Cutoff F ζ hζ U R P H)
    (χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H)
    (h₀ : IsCompact (differentialSupport F ζ hζ U R P H χ₀))
    (hχ : ∀ c, IsCompact (differentialSupport F ζ hζ U R P H (χ c))) :
    HasCompactSupport (collarError F ζ hζ U R P H χ₀ χ) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, collarError F ζ hζ U R P H χ₀ χ x ≤ C := by
  have h₀' : HasCompactSupport (differentialNormSquared F ζ hζ U R P H χ₀) := by
    rw [HasCompactSupport, ← differentialSupport_eq_tsupport]; exact h₀
  have hχ' : ∀ c, HasCompactSupport (differentialNormSquared F ζ hζ U R P H (χ c)) := by
    intro c
    rw [HasCompactSupport, ← differentialSupport_eq_tsupport]; exact hχ c
  have hsum : ∀ s : Finset (CuspIndex F ζ hζ U R P H),
      HasCompactSupport (fun x => ∑ c ∈ s, differentialNormSquared F ζ hζ U R P H (χ c) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hχ' a).add ih
  have hc : HasCompactSupport (collarError F ζ hζ U R P H χ₀ χ) :=
    h₀'.add (hsum Finset.univ)
  have hcont := (collarError_continuous_nonnegative F ζ hζ U R P H χ₀ χ).1
  obtain ⟨C, hC⟩ := hcont.bddAbove_range_of_hasCompactSupport hc
  refine ⟨hc, max C 0, le_max_right _ _, fun x => ?_⟩
  exact (hC (Set.mem_range_self x)).trans (le_max_left _ _)

structure SquareEndPartition (T : ℝ) where
  χ₀ : Cutoff F ζ hζ U R P H
  χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H
  ρ : Cutoff F ζ hζ U R P H
  A : ℝ
  B : ℝ
  T_lt_A : T < A
  A_lt_B : A < B
  core_range : ∀ x, 0 ≤ χ₀.val x ∧ χ₀.val x ≤ 1
  cusp_range : ∀ c x, 0 ≤ (χ c).val x ∧ (χ c).val x ≤ 1
  square_sum : ∀ x, χ₀.val x ^ 2 + ∑ c, (χ c).val x ^ 2 = 1
  compact_core_support : HasCompactSupport χ₀.val

  cusp_support_in_tail : ∀ c, tsupport (χ c).val ⊆
    KPContActualCollarBuffer.endSet F ζ hζ U R P H T c

  cusp_zero_off_own_end : ∀ c x,
    x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H A c → (χ c).val x = 0
  cusp_zero_other_ends : ∀ c c', c ≠ c' → ∀ x,
    x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H T c' → (χ c).val x = 0
  cusp_one_high : ∀ c (z : KPCuspCharts.Coordinates F), B ≤ z.2 →
    (χ c).val (KPContActualCollarBuffer.chartLift F ζ hζ U R P H c z) = 1
  core_one_below : ∀ x,
    (∀ c, x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H A c) → χ₀.val x = 1
  core_zero_high : ∀ c (z : KPCuspCharts.Coordinates F), B ≤ z.2 →
    χ₀.val (KPContActualCollarBuffer.chartLift F ζ hζ U R P H c z) = 0
  compact_core_differential : IsCompact (differentialSupport F ζ hζ U R P H χ₀)
  compact_cusp_differential : ∀ c,
    IsCompact (differentialSupport F ζ hζ U R P H (χ c))
  error_nonnegative : ∀ x, 0 ≤ collarError F ζ hζ U R P H χ₀ χ x
  error_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, collarError F ζ hζ U R P H χ₀ χ x ≤ C
  compact_error_support : HasCompactSupport (collarError F ζ hζ U R P H χ₀ χ)
  rho_range : ∀ x, 0 ≤ ρ.val x ∧ ρ.val x ≤ 1
  compact_rho_support : HasCompactSupport ρ.val

  rho_one_neighborhood : ∃ V : Set (Base F ζ hζ U), IsOpen V ∧
    tsupport χ₀.val ∪ tsupport (collarError F ζ hζ U R P H χ₀ χ) ⊆ V ∧
    ∀ x ∈ V, ρ.val x = 1
  core_multiplier : SectorMultiplier F ζ hζ U R P H χ₀
  cusp_multiplier : ∀ c, SectorMultiplier F ζ hζ U R P H (χ c)
  rho_multiplier : SectorMultiplier F ζ hζ U R P H ρ
  core_multiplier_contraction : ‖core_multiplier.op‖ ≤ 1
  cusp_multiplier_contraction : ∀ c, ‖(cusp_multiplier c).op‖ ≤ 1
  rho_multiplier_contraction : ‖rho_multiplier.op‖ ≤ 1

  no_ends : IsEmpty (CuspIndex F ζ hζ U R P H) →
    IsCompact (Set.univ : Set (Base F ζ hζ U)) ∧
      (∀ x, χ₀.val x = 1) ∧ (∀ x, ρ.val x = 1)

section ConstructionHelpers

 def angle (A B t : ℝ) := (Real.pi / 2) * Real.smoothTransition ((t-A)/(B-A))
private theorem angle_smooth (A B : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (angle A B) := by
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))
private theorem angle_zero {A B t : ℝ} (hAB : A < B) (ht : t ≤ A) : angle A B t = 0 := by
  unfold angle
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (le_of_lt (sub_pos.mpr hAB))), mul_zero]
private theorem angle_one {A B t : ℝ} (hAB : A < B) (ht : B ≤ t) : angle A B t = Real.pi / 2 := by
  unfold angle
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hAB)).mpr (by linarith)), mul_one]
private theorem angle_range (A B t : ℝ) : 0 ≤ angle A B t ∧ angle A B t ≤ Real.pi / 2 := by
  have hp := le_of_lt Real.pi_pos
  constructor
  · exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg _)
  · exact mul_le_of_le_one_right (by positivity) (Real.smoothTransition.le_one _)
private theorem sin_range (A B t : ℝ) : 0 ≤ Real.sin (angle A B t) ∧ Real.sin (angle A B t) ≤ 1 := by
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi (angle_range A B t).1 (by have := (angle_range A B t).2; have := Real.pi_pos; linarith), Real.sin_le_one _⟩
private theorem cos_range (A B t : ℝ) : 0 ≤ Real.cos (angle A B t) ∧ Real.cos (angle A B t) ≤ 1 := by
  exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by have := (angle_range A B t).1; have := Real.pi_pos; linarith, (angle_range A B t).2⟩, Real.cos_le_one _⟩

private theorem multiplier_contraction (η : Cutoff F ζ hζ U R P H)
    (hη : ∀ x, |η.val x| ≤ 1) (m : SectorMultiplier F ζ hζ U R P H η) : ‖m.op‖ ≤ 1 := by
  refine m.op.opNorm_le_bound zero_le_one fun u => ?_
  change ‖(m.op u).val‖ ≤ 1 * ‖u.val‖
  rw [one_mul, Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top u.val)
  apply eLpNorm_mono_ae (Lp.aestronglyMeasurable (m.op u).val)
  filter_upwards [m.ae_apply u] with x hx
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hη _)

 def sumCutoff {ι : Type*} (s : Finset ι) (η : ι → Cutoff F ζ hζ U R P H) : Cutoff F ζ hζ U R P H :=
  ⟨fun x => ∑ i ∈ s, (η i).val x, fun a => by
    choose g hg he using (fun i => (η i).smooth a)
    refine ⟨fun x => ∑ i ∈ s, g i x, ?_, ?_⟩
    · exact ContDiffOn.sum (fun i _ => hg i)
    · intro x; simp only [he]⟩
private theorem differential_zero_of_germ (η : Cutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) (r : ℝ)
    (he : (fun y => η.val (q a y)) =ᶠ[𝓝 x.val] (fun _ => r)) :
    cutoffDifferential η a x = 0 := by
  have hopen : IsOpen (omega a) := by
    exact a.domain_open.preimage (by
      apply continuous_pi
      intro k
      exact (continuous_apply _).comp (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).continuous)
  have hext : liftExtension a (cutoffLift η a) =ᶠ[𝓝 x.val] (fun _ => (r : ℂ)) := by
    filter_upwards [he, hopen.mem_nhds x.property] with y hy hmem
    simp only [liftExtension, dite_eq_left hmem, cutoffLift,hy]
  ext ⟨i,k⟩
  fin_cases k <;> simp [cutoffDifferential, chartDifferential, CotangentLogCoframe.j,
    HyperbolicChart.differential, HyperbolicChart.coordinateDerivative, hext.fderiv_eq]

private theorem endChart_continuous (τ : ℝ) (c : CuspIndex F ζ hζ U R P H) :
    Continuous (KPContActualCollarBuffer.endChart F ζ hζ U R P H τ c) := by
  apply Continuous.comp _ (show Continuous (KPFiniteCuspAtlas.endMap F
    (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
    (((H.atlas U).cuspAtlas c.1).cusp c.2)
    (((H.atlas U).cuspAtlas c.1).representative c.2) τ) from ?_)
  · have hh := (H.atlas U).components.continuous.comp (continuous_sigmaMk (i := c.1))
    simpa only [Function.comp_def, (H.atlas U).components_formula] using hh
  · apply Continuous.quotient_lift
    have hact : Continuous (KPCuspSiegel.action F (((H.atlas U).cuspAtlas c.1).representative c.2)) :=
      (by unfold KPCuspSiegel.action KPCuspSiegel.glAction
          exact (KPArch.productAction_contDiff _ _).continuous)
    exact continuous_quotient_mk'.comp
      (hact.comp ((KPCuspCharts.toArch_contDiff F).continuous.comp continuous_subtype_val))
private theorem compact_slab (c : CuspIndex F ζ hζ U R P H) (L B : ℝ) :
    ∃ K : Set (Base F ζ hζ U), IsCompact K ∧
      ∀ z : KPCuspCharts.Coordinates F, z.2 ∈ Set.Icc L B →
        KPContActualCollarBuffer.chartLift F ζ hζ U R P H c z ∈ K := by
  let G := ((H.atlas U).cuspAtlas c.1).geometry c.2
  let S := KPContActualCollarBuffer.Stabilizer F ζ hζ U R P H c
  letI : CompactSpace (KPCuspCharts.CrossQuotient F S) := G.compact_cross
  letI : CompactSpace (Set.Icc L B) := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : KPCuspCharts.CrossQuotient F S × Set.Icc L B → Base F ζ hζ U := fun p =>
    KPContActualCollarBuffer.endChart F ζ hζ U R P H (L-1) c
      (G.highPresentation (L-1) (p.1, ⟨p.2.val, by change L-1 < p.2.val; have := p.2.property.1; linarith⟩))
  have hf : Continuous f := (endChart_continuous F ζ hζ U R P H (L-1) c).comp
    ((G.highPresentation (L-1)).continuous.comp (by fun_prop))
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro z hz
  refine ⟨(Quotient.mk _ z.1, ⟨z.2,hz⟩), ?_⟩
  dsimp only [f]
  rw [G.highPresentation_formula]
  rfl
private theorem end_lift_range (τ : ℝ) (c : CuspIndex F ζ hζ U R P H) :
    KPContActualCollarBuffer.chartLift F ζ hζ U R P H c ''
      {z : KPCuspCharts.Coordinates F | τ < z.2} =
    KPContActualCollarBuffer.endSet F ζ hζ U R P H τ c := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨KPCuspSiegel.projection F _
      (((H.atlas U).cuspAtlas c.1).representative c.2 • KPCuspCharts.toArch F z), ?_, rfl⟩
    refine ⟨_, ⟨KPCuspCharts.toArch F z, ?_, rfl⟩, rfl⟩
    change τ < KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F z)
    rw [KPCuspCharts.toArch_meanHeight F (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension]
    exact hz
  · rintro ⟨u,⟨w,⟨v,hv,rfl⟩,rfl⟩,rfl⟩
    let z := (KPCuspCharts.toArchHomeomorph F
      (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension).symm v
    refine ⟨z, hv, ?_⟩
    change KPContActualCollarBuffer.chartLift F ζ hζ U R P H c z = _
    simp only [KPContActualCollarBuffer.chartLift]
    congr 2
    exact congrArg (fun w => (((H.atlas U).cuspAtlas c.1).representative c.2 • w))
      ((KPCuspCharts.toArchHomeomorph F _).apply_symm_apply v)
private theorem ends_antitone {s t : ℝ} (hst : s ≤ t)
    (c : CuspIndex F ζ hζ U R P H) :
    KPContActualCollarBuffer.endSet F ζ hζ U R P H t c ⊆
      KPContActualCollarBuffer.endSet F ζ hζ U R P H s c := by
  rw [← end_lift_range F ζ hζ U R P H t c, ← end_lift_range F ζ hζ U R P H s c]
  exact Set.image_mono fun z hz => lt_of_le_of_lt hst hz
private theorem all_ends_open (t : ℝ) (c : CuspIndex F ζ hζ U R P H) :
    IsOpen (KPContActualCollarBuffer.endSet F ζ hζ U R P H t c) := by
  have hop : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative c.1)) := by
    have he := (H.atlas U).components.isOpenMap.comp (isOpenMap_sigmaMk (i := c.1))
    simpa only [Function.comp_def, (H.atlas U).components_formula] using he
  exact hop _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ t)
private theorem compact_truncated_core (B : ℝ) :
    IsCompact ((⋃ c : CuspIndex F ζ hζ U R P H,
      KPContActualCollarBuffer.endSet F ζ hζ U R P H B c)ᶜ) := by
  classical
  choose K hK hslab using (fun c : CuspIndex F ζ hζ U R P H =>
    compact_slab F ζ hζ U R P H c (H.atlas U).threshold B)
  let core := (⋃ c : CuspIndex F ζ hζ U R P H,
      KPContActualCollarBuffer.endSet F ζ hζ U R P H (H.atlas U).threshold c)ᶜ
  have hc : IsCompact core := by
    convert (H.atlas U).compact_core using 1
    ext x
    simp only [core, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_univ,
      true_and, KPContActualCollarBuffer.endSet]
    simp only [Sigma.exists]
  have hcompact : IsCompact (core ∪ ⋃ c, K c) := hc.union (isCompact_iUnion hK)
  apply hcompact.of_isClosed_subset
  · exact (isOpen_iUnion (all_ends_open F ζ hζ U R P H B)).isClosed_compl
  · intro x hx
    by_cases hcore : x ∈ core
    · exact Or.inl hcore
    · right
      have hh : x ∈ ⋃ c : CuspIndex F ζ hζ U R P H,
          KPContActualCollarBuffer.endSet F ζ hζ U R P H (H.atlas U).threshold c :=
        not_not.mp hcore
      obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hh
      rw [← end_lift_range F ζ hζ U R P H (H.atlas U).threshold c] at hc
      obtain ⟨z,hz,rfl⟩ := hc
      have hzB : z.2 ≤ B := by
        by_contra hn
        apply hx
        exact Set.mem_iUnion.mpr ⟨c, by rw [← end_lift_range F ζ hζ U R P H B c]; exact ⟨z,lt_of_not_ge hn,rfl⟩⟩
      exact Set.mem_iUnion.mpr ⟨c,hslab c z ⟨hz.le,hzB⟩⟩

private theorem height_tail (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) {s : ℝ} (hs : buf.τ ≤ s) (x : Base F ζ hζ U) :
    x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H s c ↔
      x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c ∧
        s < KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x := by
  constructor
  · intro hx
    rw [← end_lift_range F ζ hζ U R P H s c] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [← buf.lift_range c]; exact ⟨z,lt_of_le_of_lt hs hz,rfl⟩
    · rw [buf.height_coordinates c z (lt_of_le_of_lt hs hz)]; exact hz
  · rintro ⟨hx,hheight⟩
    rw [← buf.lift_range c] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    rw [buf.height_coordinates c z hz] at hheight
    rw [← end_lift_range F ζ hζ U R P H s c]
    exact ⟨z,hheight,rfl⟩
private theorem zero_extension_off (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (φ : ℝ → ℝ) {s : ℝ} (hs : buf.τ ≤ s)
    (hφ : ∀ t, t ≤ s → φ t = 0) (x : Base F ζ hζ U)
    (hx : x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H s c) :
    KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x = 0 := by
  by_cases he : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
  · have ht : KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x ≤ s := by
      by_contra hn
      exact hx ((height_tail F ζ hζ U R P H D buf c hs x).mpr ⟨he,lt_of_not_ge hn⟩)
    simpa only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem he] using hφ _ ht
  · simp [KPContActualCollarBuffer.zeroExtension,he]
private theorem zero_extension_support_tail (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (φ : ℝ → ℝ) {s t : ℝ}
    (ht : buf.τ ≤ t) (hts : t < s) (hDs : D ≤ s)
    (hφ : ∀ u, u ≤ s → φ u = 0) :
    tsupport (KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ) ⊆
      KPContActualCollarBuffer.endSet F ζ hζ U R P H t c := by
  intro x hx
  by_contra hnot
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
  by_cases hc : x ∈ closure (KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c)
  · by_cases he : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
    · have ht' : KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x ≤ t := by
        by_contra hn
        exact hnot ((height_tail F ζ hζ U R P H D buf c ht x).mpr ⟨he,lt_of_not_ge hn⟩)
      have hcont := (buf.height_continuous c x he).continuousAt ((buf.open_ends c).mem_nhds he)
      have hsmall := (isOpen_Iio.mem_nhds (lt_of_le_of_lt ht' hts))
      filter_upwards [hcont hsmall, (buf.open_ends c).mem_nhds he] with y hy hmem
      simp only [KPContActualCollarBuffer.zeroExtension,Set.indicator_of_mem hmem,Pi.zero_apply]
      exact hφ _ hy.le
    · have hf : x ∈ frontier (KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c) := by
        rw [frontier, (buf.open_ends c).interior_eq]; exact ⟨hc,he⟩
      obtain ⟨V,hV,hxV,hbound⟩ := buf.boundary_height_buffer c x hf
      filter_upwards [hV.mem_nhds hxV] with y hy
      by_cases hyE : y ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
      · simp only [KPContActualCollarBuffer.zeroExtension,Set.indicator_of_mem hyE,Pi.zero_apply]
        exact hφ _ ((hbound y hy hyE).le.trans hDs)
      · simp [KPContActualCollarBuffer.zeroExtension,hyE]
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
    have he : y ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c := fun he => hy (subset_closure he)
    simp [KPContActualCollarBuffer.zeroExtension,he]

private theorem compact_differential_of_end_plateaus (η : Cutoff F ζ hζ U R P H)
    (B : ℝ) (hp : ∀ c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c,
      η.val x = r) : IsCompact (differentialSupport F ζ hζ U R P H η) := by
  apply (compact_truncated_core F ζ hζ U R P H B).of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isOpen_iUnion (all_ends_open F ζ hζ U R P H B)).isClosed_compl)
  rintro x ⟨a,y,rfl,hy⟩
  intro hx
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
  obtain ⟨r,hr⟩ := hp c
  have he : (fun z => η.val (q a z)) =ᶠ[𝓝 y.val] (fun _ => r) := by
    filter_upwards [((all_ends_open F ζ hζ U R P H B c).preimage (continuous_q a)).mem_nhds hc] with z hz
    exact hr _ hz
  exact hy (differential_zero_of_germ F ζ hζ U R P H η a y r he)

 def subCutoff (η ξ : Cutoff F ζ hζ U R P H) : Cutoff F ζ hζ U R P H :=
  ⟨η.val - ξ.val, fun a => by
    obtain ⟨g,hg,he⟩ := η.smooth a
    obtain ⟨k,hk,hke⟩ := ξ.smooth a
    exact ⟨g-k,hg.sub hk,fun x => by simp only [Pi.sub_apply,he,hke]⟩⟩

private theorem extension_other (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    {c c' : CuspIndex F ζ hζ U R P H} (hcc : c ≠ c') (φ : ℝ → ℝ)
    (x : Base F ζ hζ U) (hx : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c') :
    KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x = 0 := by
  have hn : x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c := by
    intro hc
    exact Set.disjoint_left.mp (buf.disjoint_ends hcc) hc hx
  simp [KPContActualCollarBuffer.zeroExtension,hn]
private theorem extension_sum_at (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (c : CuspIndex F ζ hζ U R P H) (x : Base F ζ hζ U)
    (hx : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c) :
    (∑ c', KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c' φ x) =
      φ (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x) := by
  rw [Finset.sum_eq_single c]
  · simp only [KPContActualCollarBuffer.zeroExtension,Set.indicator_of_mem hx]
  · intro b _ hbc
    exact extension_other F ζ hζ U R P H D buf hbc φ x hx
  · simp
private theorem compact_core_from_plateau (η : Cutoff F ζ hζ U R P H) (B : ℝ)
    (hp : ∀ c x, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c → η.val x = 0) :
    HasCompactSupport η.val := by
  apply (compact_truncated_core F ζ hζ U R P H B).of_isClosed_subset (isClosed_tsupport η.val)
  apply closure_minimal _ ((isOpen_iUnion (all_ends_open F ζ hζ U R P H B)).isClosed_compl)
  intro x hx hn
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hn
  exact hx (hp c x hc)

private theorem differentialSupport_in_core (η : Cutoff F ζ hζ U R P H)
    (B : ℝ) (hp : ∀ c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c,
      η.val x = r) : differentialSupport F ζ hζ U R P H η ⊆
      (⋃ c : CuspIndex F ζ hζ U R P H, KPContActualCollarBuffer.endSet F ζ hζ U R P H B c)ᶜ := by
  apply closure_minimal _ ((isOpen_iUnion (all_ends_open F ζ hζ U R P H B)).isClosed_compl)
  rintro x ⟨a,y,rfl,hy⟩ hx
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
  obtain ⟨r,hr⟩ := hp c
  have he : (fun z => η.val (q a z)) =ᶠ[𝓝 y.val] (fun _ => r) := by
    filter_upwards [((all_ends_open F ζ hζ U R P H B c).preimage (continuous_q a)).mem_nhds hc] with z hz
    exact hr _ hz
  exact hy (differential_zero_of_germ F ζ hζ U R P H η a y r he)
private theorem norm_zero_off_differentialSupport (η : Cutoff F ζ hζ U R P H)
    (x : Base F ζ hζ U) (hx : x ∉ differentialSupport F ζ hζ U R P H η) :
    differentialNormSquared F ζ hζ U R P H η x = 0 := by
  rw [differentialSupport_eq_tsupport] at hx
  exact image_eq_zero_of_notMem_tsupport hx
private theorem error_support_core (χ₀ : Cutoff F ζ hζ U R P H)
    (χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H) (B : ℝ)
    (h₀ : ∀ c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c, χ₀.val x = r)
    (hχ : ∀ k c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c, (χ k).val x = r) :
    tsupport (collarError F ζ hζ U R P H χ₀ χ) ⊆
      (⋃ c : CuspIndex F ζ hζ U R P H, KPContActualCollarBuffer.endSet F ζ hζ U R P H B c)ᶜ := by
  apply closure_minimal _ ((isOpen_iUnion (all_ends_open F ζ hζ U R P H B)).isClosed_compl)
  intro x hx hhigh
  have hn₀ : x ∉ differentialSupport F ζ hζ U R P H χ₀ :=
    fun hh => differentialSupport_in_core F ζ hζ U R P H χ₀ B h₀ hh hhigh
  have hnχ : ∀ k, x ∉ differentialSupport F ζ hζ U R P H (χ k) :=
    fun k hh => differentialSupport_in_core F ζ hζ U R P H (χ k) B (hχ k) hh hhigh
  apply hx
  simp only [collarError, norm_zero_off_differentialSupport F ζ hζ U R P H χ₀ x hn₀,
    norm_zero_off_differentialSupport F ζ hζ U R P H (χ _) x (hnχ _), Finset.sum_const_zero, add_zero]

private theorem closure_end_inside (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (s t : ℝ) (hDs : D ≤ s) (hst : s < t) :
    closure (KPContActualCollarBuffer.endSet F ζ hζ U R P H t c) ⊆
      KPContActualCollarBuffer.endSet F ζ hζ U R P H s c := by
  let m := (s+t)/2
  let φ := fun u => Real.smoothTransition ((u-m)/(t-m))
  have hsm : s < m := by dsimp [m]; linarith
  have hmt : m < t := by dsimp [m]; linarith
  have hzero : ∀ u, u ≤ m → φ u = 0 := by
    intro u hu
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (sub_nonneg.mpr hmt.le))
  apply Set.Subset.trans (closure_mono ?_) (zero_extension_support_tail F ζ hζ U R P H D buf c φ
    (buf.below_cutoff.le.trans hDs) hsm (hDs.trans hsm.le) hzero)
  intro x hx
  have hh := (height_tail F ζ hζ U R P H D buf c (buf.below_cutoff.le.trans (hDs.trans hst.le)) x).mp hx
  change KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x ≠ 0
  simp only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem hh.1]
  have hone : φ (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x) = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hmt)).mpr (by linarith [hh.2]))
  rw [hone]; exact one_ne_zero
private theorem core_in_open_lower (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (s t : ℝ) (hDs : D ≤ s) (hst : s < t) :
    (⋃ c : CuspIndex F ζ hζ U R P H, KPContActualCollarBuffer.endSet F ζ hζ U R P H s c)ᶜ ⊆
      (⋃ c : CuspIndex F ζ hζ U R P H, closure (KPContActualCollarBuffer.endSet F ζ hζ U R P H t c))ᶜ := by
  intro x hx hh
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hh
  exact hx (Set.mem_iUnion.mpr ⟨c,closure_end_inside F ζ hζ U R P H D buf c s t hDs hst hc⟩)

end ConstructionHelpers

section Constant

def oneCutoff : Cutoff F ζ hζ U R P H :=
  ⟨fun _ => 1, fun a => ⟨fun _ => 1, contDiffOn_const, fun _ => rfl⟩⟩

private theorem oneCutoff_differential (a : ActualChart (U := U) (H := H)) (x : omega a) :
    cutoffDifferential (oneCutoff F ζ hζ U R P H) a x = 0 := by
  have hopen : IsOpen (omega a) := by
    exact a.domain_open.preimage (by
      apply continuous_pi
      intro k
      exact (continuous_apply _).comp
        (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).continuous)
  have he : liftExtension a (cutoffLift (oneCutoff F ζ hζ U R P H) a) =ᶠ[𝓝 x.val]
      (fun _ => (1:ℂ)) := by
    filter_upwards [hopen.mem_nhds x.property] with y hy
    simp [liftExtension, cutoffLift, oneCutoff, hy]
  have hd := he.fderiv_eq (𝕜 := ℝ)

  ext i
  rcases i with ⟨i,k⟩
  fin_cases k <;>
    simp [cutoffDifferential, chartDifferential, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, CotangentLogCoframe.j, hd]

private theorem oneCutoff_norm :
    differentialNormSquared F ζ hζ U R P H (oneCutoff F ζ hζ U R P H) = 0 := by
  symm
  apply (Classical.choose_spec
    (differentialNormSquared_descends F ζ hζ U R P H (oneCutoff F ζ hζ U R P H))).2
  refine ⟨continuous_const, ?_⟩
  intro a x
  simp only [Pi.zero_apply, oneCutoff_differential, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0)]

private theorem oneCutoff_support :
    differentialSupport F ζ hζ U R P H (oneCutoff F ζ hζ U R P H) = ∅ := by
  rw [differentialSupport_eq_tsupport, oneCutoff_norm]
  exact tsupport_zero

def oneMultiplier : SectorMultiplier F ζ hζ U R P H (oneCutoff F ζ hζ U R P H) where
  op := ContinuousLinearMap.id ℂ _
  ae_apply := fun u => Filter.Eventually.of_forall (fun x => by
    simp only [ContinuousLinearMap.id_apply, oneCutoff, one_mul, Complex.ofReal_one])
  test_commutes := by
    intro f
    have he : scalarMultiply (oneCutoff F ζ hζ U R P H) f = f := by
      apply Subtype.ext
      funext a x
      simp [scalarMultiply, cutoffLift, oneCutoff]
    rw [he]
    rfl
  ordinary_central_invariant := fun _ _ => rfl
  genuine_unchanged := by
    intro f ε x
    simpa only [oneCutoff, Complex.ofReal_one, one_mul,
      KPContSectorCoveredQuotientVocabulary.chi_coe] using f.property ε x

theorem squareEndPartition_no_ends (T : ℝ) [IsEmpty (CuspIndex F ζ hζ U R P H)] :
    Nonempty (SquareEndPartition F ζ hζ U R P H T) := by
  have hcompact : IsCompact (Set.univ : Set (Base F ζ hζ U)) := by
    have hends : (⋃ i : Fin (H.atlas U).componentCount, ⋃ a : Fin ((H.atlas U).cuspAtlas i).cuspCount,
        KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) ''
          KPFiniteCuspAtlas.endSet F
            (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
            (((H.atlas U).cuspAtlas i).representative a) (H.atlas U).threshold) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      exact isEmptyElim (⟨i,a⟩ : CuspIndex F ζ hζ U R P H)
    simpa only [hends, Set.diff_empty] using (H.atlas U).compact_core
  let η := oneCutoff F ζ hζ U R P H
  let χ : CuspIndex F ζ hζ U R P H → Cutoff F ζ hζ U R P H := fun c => isEmptyElim c
  have herror : collarError F ζ hζ U R P H η χ = 0 := by
    funext x
    simp [collarError, η, oneCutoff_norm]
  have hηcompact : HasCompactSupport η.val := by
    apply hcompact.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have hop : ‖(oneMultiplier F ζ hζ U R P H).op‖ ≤ 1 := by
    apply ((oneMultiplier F ζ hζ U R P H).op).opNorm_le_bound (by norm_num)
    intro u
    change ‖u‖ ≤ 1 * ‖u‖
    simp
  refine ⟨{ χ₀ := η
            χ := χ
            ρ := η
            A := T + 1
            B := T + 2

            T_lt_A := by linarith
            A_lt_B := by linarith
            core_range := fun x => by simp [η, oneCutoff]
            cusp_range := fun c => isEmptyElim c
            square_sum := fun x => by simp [η, oneCutoff]
            compact_core_support := hηcompact
            cusp_support_in_tail := fun c => isEmptyElim c
            cusp_zero_off_own_end := fun c => isEmptyElim c
            cusp_zero_other_ends := fun c => isEmptyElim c
            cusp_one_high := fun c => isEmptyElim c
            core_one_below := fun _ _ => rfl
            core_zero_high := fun c => isEmptyElim c
            compact_core_differential := by
              dsimp only [η]
              rw [oneCutoff_support]
              exact isCompact_empty
            compact_cusp_differential := fun c => isEmptyElim c
            error_nonnegative := fun x => by rw [herror]; exact le_rfl
            error_bounded := ⟨0, le_rfl, fun x => by rw [herror]; exact le_rfl⟩
            compact_error_support := by rw [herror]; exact HasCompactSupport.zero
            rho_range := fun x => by simp [η, oneCutoff]
            compact_rho_support := hηcompact
            rho_one_neighborhood := ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun _ _ => rfl⟩
            core_multiplier := oneMultiplier F ζ hζ U R P H
            cusp_multiplier := fun c => isEmptyElim c
            rho_multiplier := oneMultiplier F ζ hζ U R P H
            core_multiplier_contraction := hop
            cusp_multiplier_contraction := fun c => isEmptyElim c
            rho_multiplier_contraction := hop
            no_ends := fun _ => ⟨hcompact, fun _ => rfl, fun _ => rfl⟩ }⟩
end Constant

section RadialConstruction
 def radialCutoff (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hz : ∀ t, t ≤ D → φ t = 0) : Cutoff F ζ hζ U R P H :=
  Classical.choose (KPContActualRadialCutoff.exists_smooth_zero_extension F ζ hζ U R P H D buf c φ hφ hz)
private theorem radialCutoff_val (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (c : CuspIndex F ζ hζ U R P H) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hz : ∀ t, t ≤ D → φ t = 0) :
    (radialCutoff F ζ hζ U R P H D buf c φ hφ hz).val =
      KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ :=
  (Classical.choose_spec (KPContActualRadialCutoff.exists_smooth_zero_extension F ζ hζ U R P H D buf c φ hφ hz)).1
 def complementRadial (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0) : Cutoff F ζ hζ U R P H :=
  subCutoff F ζ hζ U R P H (oneCutoff F ζ hζ U R P H)
    (sumCutoff F ζ hζ U R P H Finset.univ (fun c => radialCutoff F ζ hζ U R P H D buf c φ hφ hz))
private theorem complementRadial_val (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0) (x : Base F ζ hζ U) :
    (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x =
      1 - ∑ c, KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x := by
  simp only [complementRadial,subCutoff,oneCutoff,sumCutoff,Pi.sub_apply,radialCutoff_val]
private theorem complementRadial_on_end (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (c : CuspIndex F ζ hζ U R P H) (x : Base F ζ hζ U)
    (hx : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c) :
    (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x =
      1 - φ (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x) := by
  rw [complementRadial_val, extension_sum_at F ζ hζ U R P H D buf φ c x hx]
private theorem complementRadial_one_off (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (s : ℝ) (hs : D ≤ s) (hzs : ∀ t, t ≤ s → φ t = 0) (x : Base F ζ hζ U)
    (hx : ∀ c, x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H s c) :
    (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x = 1 := by
  rw [complementRadial_val]
  have he : ∀ c, KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buf.τ c φ x = 0 :=
    fun c => zero_extension_off F ζ hζ U R P H D buf c φ (buf.below_cutoff.le.trans hs) hzs x (hx c)
  simp only [he,Finset.sum_const_zero,sub_zero]
private theorem complementRadial_range (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (hr : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (x : Base F ζ hζ U) :
    0 ≤ (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x ∧
      (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x ≤ 1 := by
  by_cases he : ∃ c, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
  · obtain ⟨c,hc⟩ := he
    rw [complementRadial_on_end F ζ hζ U R P H D buf φ hφ hz c x hc]
    have := hr (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x)
    constructor <;> linarith
  · have hx : ∀ c, x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H D c := by
      intro c hc; exact he ⟨c, ends_antitone F ζ hζ U R P H buf.below_cutoff.le c hc⟩
    rw [complementRadial_one_off F ζ hζ U R P H D buf φ hφ hz D le_rfl hz x hx]
    exact ⟨zero_le_one,le_rfl⟩

private theorem complementRadial_high (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (B : ℝ) (hDB : D ≤ B) (hone : ∀ t, B ≤ t → φ t = 1)
    (c : CuspIndex F ζ hζ U R P H) (x : Base F ζ hζ U)
    (hx : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c) :
    (complementRadial F ζ hζ U R P H D buf φ hφ hz).val x = 0 := by
  have hh := (height_tail F ζ hζ U R P H D buf c (buf.below_cutoff.le.trans hDB) x).mp hx
  rw [complementRadial_on_end F ζ hζ U R P H D buf φ hφ hz c x hh.1, hone _ hh.2.le, sub_self]
private theorem radial_range (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (hr : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1)
    (c : CuspIndex F ζ hζ U R P H) (x : Base F ζ hζ U) :
    0 ≤ (radialCutoff F ζ hζ U R P H D buf c φ hφ hz).val x ∧
      (radialCutoff F ζ hζ U R P H D buf c φ hφ hz).val x ≤ 1 := by
  rw [radialCutoff_val]
  by_cases he : x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
  · simpa only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem he] using hr (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x)
  · simp [KPContActualCollarBuffer.zeroExtension,he]
private theorem radial_plateau (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (B : ℝ) (hDB : D ≤ B) (hone : ∀ t, B ≤ t → φ t = 1)
    (c : CuspIndex F ζ hζ U R P H) :
    ∀ c', ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c',
      (radialCutoff F ζ hζ U R P H D buf c φ hφ hz).val x = r := by
  intro c'
  by_cases hc : c = c'
  · subst c'
    refine ⟨1,fun x hx => ?_⟩
    rw [radialCutoff_val]
    have hh := (height_tail F ζ hζ U R P H D buf c (buf.below_cutoff.le.trans hDB) x).mp hx
    simp only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem hh.1]
    exact hone _ hh.2.le
  · refine ⟨0,fun x hx => ?_⟩
    rw [radialCutoff_val]
    exact extension_other F ζ hζ U R P H D buf hc φ x
      (ends_antitone F ζ hζ U R P H (buf.below_cutoff.le.trans hDB) c' hx)

private theorem sin_profile_smooth (A B : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun t => Real.sin (angle A B t)) :=
  Real.contDiff_sin.comp (angle_smooth A B)
private theorem cos_complement_smooth (A B : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun t => 1 - Real.cos (angle A B t)) :=
  contDiff_const.sub (Real.contDiff_cos.comp (angle_smooth A B))
private theorem transition_smooth (A B : ℝ) : ContDiff ℝ (⊤ : ℕ∞)
    (fun t => Real.smoothTransition ((t-A)/(B-A))) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
private theorem cos_complement_zero {A B : ℝ} (hAB : A < B) : ∀ t, t ≤ A → 1 - Real.cos (angle A B t) = 0 := by
  intro t ht; rw [angle_zero hAB ht,Real.cos_zero,sub_self]
private theorem sin_profile_zero {A B : ℝ} (hAB : A < B) : ∀ t, t ≤ A → Real.sin (angle A B t) = 0 := by
  intro t ht; rw [angle_zero hAB ht,Real.sin_zero]
private theorem cos_complement_one {A B : ℝ} (hAB : A < B) : ∀ t, B ≤ t → 1 - Real.cos (angle A B t) = 1 := by
  intro t ht; rw [angle_one hAB ht,Real.cos_pi_div_two,sub_zero]
private theorem sin_profile_one {A B : ℝ} (hAB : A < B) : ∀ t, B ≤ t → Real.sin (angle A B t) = 1 := by
  intro t ht; rw [angle_one hAB ht,Real.sin_pi_div_two]
private theorem cos_complement_range (A B : ℝ) : ∀ t, 0 ≤ 1 - Real.cos (angle A B t) ∧ 1 - Real.cos (angle A B t) ≤ 1 := by
  intro t; have := cos_range A B t; constructor <;> linarith
private theorem cutoff_core_support (η : Cutoff F ζ hζ U R P H) (B : ℝ)
    (hp : ∀ c x, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c → η.val x = 0) :
    tsupport η.val ⊆ (⋃ c : CuspIndex F ζ hζ U R P H, KPContActualCollarBuffer.endSet F ζ hζ U R P H B c)ᶜ := by
  apply closure_minimal _ ((isOpen_iUnion (all_ends_open F ζ hζ U R P H B)).isClosed_compl)
  intro x hx hn
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hn
  exact hx (hp c x hc)
private theorem radial_at_coordinate (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hz : ∀ t, t ≤ D → φ t = 0)
    (c : CuspIndex F ζ hζ U R P H) (z : KPCuspCharts.Coordinates F) (hzheight : buf.τ < z.2) :
    (radialCutoff F ζ hζ U R P H D buf c φ hφ hz).val
      (KPContActualCollarBuffer.chartLift F ζ hζ U R P H c z) = φ z.2 := by
  rw [radialCutoff_val]
  have he : KPContActualCollarBuffer.chartLift F ζ hζ U R P H c z ∈
      KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c := by
    rw [← buf.lift_range c]; exact ⟨z,hzheight,rfl⟩
  simp only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem he,
    buf.height_coordinates c z hzheight]

private theorem square_sum_radial (D : ℝ) (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H D)
    (A B : ℝ) (hAB : A < B) (hDA : D ≤ A) (x : Base F ζ hζ U) :
    (complementRadial F ζ hζ U R P H D buf (fun t => 1 - Real.cos (angle A B t))
      (cos_complement_smooth A B) (fun t ht => cos_complement_zero hAB t (ht.trans hDA))).val x ^ 2 +
    ∑ c, (radialCutoff F ζ hζ U R P H D buf c (fun t => Real.sin (angle A B t))
      (sin_profile_smooth A B) (fun t ht => sin_profile_zero hAB t (ht.trans hDA))).val x ^ 2 = 1 := by
  by_cases he : ∃ c, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c
  · obtain ⟨c,hc⟩ := he
    rw [complementRadial_on_end F ζ hζ U R P H D buf _ _ _ c x hc]
    have heq : ∑ k, (radialCutoff F ζ hζ U R P H D buf k (fun t => Real.sin (angle A B t))
        (sin_profile_smooth A B) (fun t ht => sin_profile_zero hAB t (ht.trans hDA))).val x ^ 2 =
        Real.sin (angle A B (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x)) ^ 2 := by
      rw [Finset.sum_eq_single c]
      · rw [radialCutoff_val]
        simp only [KPContActualCollarBuffer.zeroExtension,Set.indicator_of_mem hc]
      · intro k _ hkc
        rw [radialCutoff_val,extension_other F ζ hζ U R P H D buf hkc _ x hc]
        norm_num
      · simp
    rw [heq]
    have hid := Real.sin_sq_add_cos_sq (angle A B (KPContActualCollarBuffer.height F ζ hζ U R P H buf.τ c x))
    nlinarith
  · have hn : ∀ c, x ∉ KPContActualCollarBuffer.endSet F ζ hζ U R P H buf.τ c := fun c hc => he ⟨c,hc⟩
    rw [complementRadial_val]
    simp only [radialCutoff_val, KPContActualCollarBuffer.zeroExtension,Set.indicator_of_notMem (hn _)]
    norm_num

set_option maxHeartbeats 800000 in
private theorem construct_with_buffer (T : ℝ)
    (buf : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H T) :
    Nonempty (SquareEndPartition F ζ hζ U R P H T) := by
  classical
  let A := T+1
  let B := T+2
  have hTA : T < A := by dsimp [A]; linarith
  have hAB : A < B := by dsimp [A,B]; linarith
  have hTB : T ≤ B := hTA.le.trans hAB.le
  let φ := fun t => Real.sin (angle A B t)
  let ψ := fun t => 1 - Real.cos (angle A B t)
  have hφ := sin_profile_smooth A B
  have hψ := cos_complement_smooth A B
  have hzφ : ∀ t, t ≤ T → φ t = 0 := fun t ht => sin_profile_zero hAB t (ht.trans hTA.le)
  have hzψ : ∀ t, t ≤ T → ψ t = 0 := fun t ht => cos_complement_zero hAB t (ht.trans hTA.le)
  let χ := fun c => radialCutoff F ζ hζ U R P H T buf c φ hφ hzφ
  let χ₀ := complementRadial F ζ hζ U R P H T buf ψ hψ hzψ
  have hcoreRange := complementRadial_range F ζ hζ U R P H T buf ψ hψ hzψ (cos_complement_range A B)
  have hcuspRange := radial_range F ζ hζ U R P H T buf φ hφ hzφ (sin_range A B)
  have hcoreHigh : ∀ c x, x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c → χ₀.val x = 0 :=
    complementRadial_high F ζ hζ U R P H T buf ψ hψ hzψ B hTB (cos_complement_one hAB)
  have hcorePlat : ∀ c, ∃ r : ℝ, ∀ x ∈ KPContActualCollarBuffer.endSet F ζ hζ U R P H B c, χ₀.val x = r :=
    fun c => ⟨0,hcoreHigh c⟩
  have hcuspPlat := radial_plateau F ζ hζ U R P H T buf φ hφ hzφ B hTB (sin_profile_one hAB)
  have hd₀ := compact_differential_of_end_plateaus F ζ hζ U R P H χ₀ B hcorePlat
  have hdχ := fun c => compact_differential_of_end_plateaus F ζ hζ U R P H (χ c) B (hcuspPlat c)
  obtain ⟨herr,C,hC,hbound⟩ := collarError_compact_bounded F ζ hζ U R P H χ₀ χ hd₀ hdχ
  let L := B+1
  let M := L+1
  have hBL : B < L := by dsimp [L]; linarith
  have hLM : L < M := by dsimp [M]; linarith
  have hTL : T ≤ L := hTB.trans hBL.le
  let θ := fun t => Real.smoothTransition ((t-L)/(M-L))
  have hθ := transition_smooth L M
  have hzθL : ∀ t, t ≤ L → θ t = 0 := by
    intro t ht
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hLM.le))
  have hzθ : ∀ t, t ≤ T → θ t = 0 := fun t ht => hzθL t (ht.trans hTL)
  have honeθ : ∀ t, M ≤ t → θ t = 1 := by
    intro t ht
    exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hLM)).mpr (by linarith))
  let ρ := complementRadial F ζ hζ U R P H T buf θ hθ hzθ
  have hρRange := complementRadial_range F ζ hζ U R P H T buf θ hθ hzθ
    (fun t => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
  have hρHigh := complementRadial_high F ζ hζ U R P H T buf θ hθ hzθ M (hTL.trans hLM.le) honeθ
  obtain ⟨m₀⟩ := KPContActualSectorMultiplier.boundedSectorMultiplier F ζ hζ U R P H χ₀ 1 zero_le_one
    (fun x => by rw [abs_of_nonneg (hcoreRange x).1]; exact (hcoreRange x).2)
  have hmχ := fun c => KPContActualSectorMultiplier.boundedSectorMultiplier F ζ hζ U R P H (χ c) 1 zero_le_one
    (fun x => by rw [abs_of_nonneg (hcuspRange c x).1]; exact (hcuspRange c x).2)
  let mχ := fun c => Classical.choice (hmχ c)
  obtain ⟨mρ⟩ := KPContActualSectorMultiplier.boundedSectorMultiplier F ζ hζ U R P H ρ 1 zero_le_one
    (fun x => by rw [abs_of_nonneg (hρRange x).1]; exact (hρRange x).2)
  refine ⟨{ χ₀ := χ₀, χ := χ, ρ := ρ, A := A, B := B,
            T_lt_A := hTA, A_lt_B := hAB, core_range := hcoreRange, cusp_range := hcuspRange,
            square_sum := square_sum_radial F ζ hζ U R P H T buf A B hAB hTA.le,
            compact_core_support := compact_core_from_plateau F ζ hζ U R P H χ₀ B hcoreHigh,
            cusp_support_in_tail := ?_, cusp_zero_off_own_end := ?_, cusp_zero_other_ends := ?_,
            cusp_one_high := ?_, core_one_below := ?_, core_zero_high := ?_,
            compact_core_differential := hd₀, compact_cusp_differential := hdχ,
            error_nonnegative := (collarError_continuous_nonnegative F ζ hζ U R P H χ₀ χ).2,
            error_bounded := ⟨C,hC,hbound⟩, compact_error_support := herr,
            rho_range := hρRange, compact_rho_support := compact_core_from_plateau F ζ hζ U R P H ρ M hρHigh,
            rho_one_neighborhood := ?_, core_multiplier := m₀, cusp_multiplier := mχ, rho_multiplier := mρ,
            core_multiplier_contraction := multiplier_contraction F ζ hζ U R P H χ₀
              (fun x => by rw [abs_of_nonneg (hcoreRange x).1]; exact (hcoreRange x).2) m₀,
            cusp_multiplier_contraction := fun c => multiplier_contraction F ζ hζ U R P H (χ c)
              (fun x => by rw [abs_of_nonneg (hcuspRange c x).1]; exact (hcuspRange c x).2) (mχ c),
            rho_multiplier_contraction := multiplier_contraction F ζ hζ U R P H ρ
              (fun x => by rw [abs_of_nonneg (hρRange x).1]; exact (hρRange x).2) mρ,
            no_ends := ?_ }⟩
  · intro c
    rw [radialCutoff_val]
    exact zero_extension_support_tail F ζ hζ U R P H T buf c φ buf.below_cutoff.le hTA hTA.le (sin_profile_zero hAB)
  · intro c x hx
    rw [radialCutoff_val]
    exact zero_extension_off F ζ hζ U R P H T buf c φ (buf.below_cutoff.le.trans hTA.le) (sin_profile_zero hAB) x hx
  · intro c c' hcc x hx
    rw [radialCutoff_val]
    exact extension_other F ζ hζ U R P H T buf hcc φ x
      (ends_antitone F ζ hζ U R P H buf.below_cutoff.le c' hx)
  · intro c z hz
    rw [radial_at_coordinate F ζ hζ U R P H T buf φ hφ hzφ c z
      (lt_of_lt_of_le (buf.below_cutoff.trans_le hTB) hz)]
    exact sin_profile_one hAB z.2 hz
  · intro x hx
    exact complementRadial_one_off F ζ hζ U R P H T buf ψ hψ hzψ A hTA.le (cos_complement_zero hAB) x hx
  · intro c z hz
    have hτz : buf.τ < z.2 := lt_of_lt_of_le (buf.below_cutoff.trans_le hTB) hz
    rw [complementRadial_on_end F ζ hζ U R P H T buf ψ hψ hzψ c _
      (by rw [← buf.lift_range c]; exact ⟨z,hτz,rfl⟩), buf.height_coordinates c z hτz]
    change 1 - (1 - Real.cos (angle A B z.2)) = 0
    rw [cos_complement_one hAB z.2 hz,sub_self]
  · let V := (⋃ c : CuspIndex F ζ hζ U R P H,
      closure (KPContActualCollarBuffer.endSet F ζ hζ U R P H L c))ᶜ
    refine ⟨V, (isClosed_iUnion_of_finite (fun c => isClosed_closure)).isOpen_compl, ?_, ?_⟩
    · apply Set.Subset.trans _ (core_in_open_lower F ζ hζ U R P H T buf B L hTB hBL)
      exact Set.union_subset
        (cutoff_core_support F ζ hζ U R P H χ₀ B hcoreHigh)
        (error_support_core F ζ hζ U R P H χ₀ χ B hcorePlat hcuspPlat)
    · intro x hx
      apply complementRadial_one_off F ζ hζ U R P H T buf θ hθ hzθ L hTL hzθL x
      intro c hc
      exact hx (Set.mem_iUnion.mpr ⟨c,subset_closure hc⟩)
  · intro hemp
    letI := hemp
    have hcore : ∀ x, χ₀.val x = 1 := by
      intro x
      rw [complementRadial_val]
      simp
    have hρ : ∀ x, ρ.val x = 1 := by
      intro x
      rw [complementRadial_val]
      simp
    have hc := (H.atlas U).compact_core
    have he : (⋃ i : Fin (H.atlas U).componentCount,
        ⋃ a : Fin ((H.atlas U).cuspAtlas i).cuspCount,
        KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) ''
        KPFiniteCuspAtlas.endSet F (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
          (((H.atlas U).cuspAtlas i).representative a) (H.atlas U).threshold) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hi
      exact isEmptyElim (⟨i,a⟩ : CuspIndex F ζ hζ U R P H)
    rw [he,Set.diff_empty] at hc
    exact ⟨hc,hcore,hρ⟩

end RadialConstruction

end DedekindZetaZeroFree.KPContActualSquareEndPartition

namespace DedekindZetaZeroFree

theorem kp_cont_actual_square_end_partition
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (T : ℝ) (hT : KPContActualSquareEndPartition.AboveEndStarts F ζ hζ U R P H T) :
    Nonempty (KPContActualSquareEndPartition.SquareEndPartition F ζ hζ U R P H T) := by
  classical
  by_cases he : IsEmpty (KPContActualSquareEndPartition.CuspIndex F ζ hζ U R P H)
  · letI := he
    exact KPContActualSquareEndPartition.squareEndPartition_no_ends F ζ hζ U R P H T
  · have hc : Nonempty (KPContActualSquareEndPartition.CuspIndex F ζ hζ U R P H) :=
      not_isEmpty_iff.mp he
    obtain ⟨c⟩ := hc
    have hthreshold : (H.atlas U).threshold < T := by
      rw [← (H.atlas U).common_threshold c.1]
      exact hT c
    obtain ⟨buf⟩ := kp_cont_actual_collar_buffer F ζ hζ U R P H realization T hthreshold
    exact KPContActualSquareEndPartition.construct_with_buffer F ζ hζ U R P H T buf

end DedekindZetaZeroFree

end
