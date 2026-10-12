module

public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.InteriorZeroExtension
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.NormalChartsAndHyperbolicDensity
public import DedekindZetaZeroFree.Adeles.Quotients.LineSections.ChartRestrictionDensity
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.LocalH1EnergyEstimates

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContFriedrichsTensorReynolds
open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContSectorPhaseComponentCharts
open KPContSectorCoveredQuotientVocabulary KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

open KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentRealOrthogonalComplexification

private theorem labeled_roundtrip (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) = y := by
  funext k
  simp [labeledA, labeledAInv]

 def geometricLift (a : ShrunkChart F ζ hζ U R P H) (σ : a.Isotropy) : Gamma a :=
  ⟨(σ, ((H.atlas U).line a.component).rho σ.val),
    ((H.atlas U).line a.component).finite_comparison σ.val⟩

private theorem geometricLift_phase (a : ShrunkChart F ζ hζ U R P H) (σ : a.Isotropy)
    (x : M F) :
    (isotropyArrow a (geometricLift a σ)).phase x =
      (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ) := by
  simp [Arrow.phase, isotropyArrow, geometricLift, isotropyChart, chi_coe]

private theorem geometricLift_psi (a : ShrunkChart F ζ hζ U R P H) (σ : a.Isotropy)
    (x : M F) :
    (isotropyArrow a (geometricLift a σ)).psi x =
      labeledAInv (placeEquiv F ζ hζ)
        ((σ.val : KPCuspArithmetic.PGL2 F) • labeledA (placeEquiv F ζ hζ) x) := by
  simp [Arrow.psi, coordinateMap, isotropyArrow, geometricLift, isotropyChart,
    ChartKind.representative]

private theorem geometric_mem (a : ShrunkChart F ζ hζ U R P H) (σ : a.Isotropy)
    (p : Space (KPCuspLogShape.dimension F * 3))
    (hp : coordinates F p ∈ a.domain) :
    coordinates F (overlapCoordinate F ζ hζ U R P H a.component σ.val p) ∈ a.domain := by
  have h := Set.mem_image_of_mem
    (fun y => (σ.val : KPCuspArithmetic.PGL2 F) • y) hp
  rw [a.invariant σ] at h
  simpa only [overlapCoordinate, Homeomorph.apply_symm_apply] using h

private theorem geometric_preserving (a : ShrunkChart F ζ hζ U R P H) (σ : a.Isotropy) :
    MeasurePreserving (overlapCoordinate F ζ hζ U R P H a.component σ.val)
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        ((coordinates F) ⁻¹' a.domain))
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        ((coordinates F) ⁻¹' a.domain)) := by
  have hc : MeasurePreserving (coordinates F)
      (volume.withDensity (fun p => ENNReal.ofReal (density F p)))
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) :=
    ⟨(coordinates F).continuous.measurable, metric_volume F⟩
  have hg := (hc.symm (coordinates F).toMeasurableEquiv).comp
    ((KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F σ.val.val).comp hc)
  have he : overlapCoordinate F ζ hζ U R P H a.component σ.val ⁻¹'
      ((coordinates F) ⁻¹' a.domain) = ((coordinates F) ⁻¹' a.domain) := by
    ext p
    constructor
    · intro hp
      have h := geometric_mem a σ⁻¹ _ hp
      change coordinates F p ∈ a.domain
      simpa only [overlapCoordinate, Homeomorph.apply_symm_apply, Subgroup.coe_inv,
        inv_smul_smul, Homeomorph.symm_apply_apply] using h
    · exact geometric_mem a σ p
  let : ContinuousConstSMul (KPCuspArithmetic.PGL2 F) (SymmetricSpace F) :=
    ⟨KPCuspSiegel.continuous_action F⟩
  let h := ((coordinates F).trans (Homeomorph.smul (σ.val : KPCuspArithmetic.PGL2 F))).trans (coordinates F).symm
  have hem : MeasurableEmbedding (overlapCoordinate F ζ hζ U R P H a.component σ.val) :=
    h.measurableEmbedding
  have hm := hg.restrict_preimage_emb hem ((coordinates F) ⁻¹' a.domain)
  change MeasurePreserving (overlapCoordinate F ζ hζ U R P H a.component σ.val)
    ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
      (overlapCoordinate F ζ hζ U R P H a.component σ.val ⁻¹' ((coordinates F) ⁻¹' a.domain)))
    _ at hm
  rwa [he] at hm

private theorem coefficient_mem_scalarFiber (a : ShrunkChart F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) (x : omega a) (k : Fin (d F) × Fin 3) :
    coefficient W a x k ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
  intro η hη
  let γ : Gamma a := ⟨(1, η), central_label_mem a η hη⟩
  have hγ : (isotropyArrow a γ).psi = id := by
    change (identity (isotropyChart a)).psi = id
    exact KPContCotangentActualGroupoidIdentities.identity_psi _
  have hcov := W.property.2.1 a γ x.val x.property
  have hQ : Q (isotropyArrow a γ) x.val = ContinuousLinearMap.id ℝ (V F) := by
    ext w k
    simp [Q, hγ, CotangentLogCoframe.H]
  have hphase : (isotropyArrow a γ).phase x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ η : ℂ) := by
    change (KPCuspGenuineMonodromy.chi F ζ hζ (1 * η * 1⁻¹) : ℂ) = _
    simp
  change coefficient W a ⟨_, _⟩ = twistedOperator (isotropyArrow a γ) x.val (coefficient W a x) at hcov
  have hx : (⟨(isotropyArrow a γ).psi x.val, isotropy_mem a γ x.val x.property⟩ : omega a) = x := by
    apply Subtype.ext
    exact congrFun hγ x.val
  rw [hx] at hcov
  simp only [twistedOperator, hQ, hphase, operatorComplexification_id,
    smul_apply, ContinuousLinearMap.id_apply] at hcov
  have hk := congrArg (fun v : E F => v k) hcov
  exact hk.symm

 def orthGradient (f : M F → ℂ) (x : M F) : E F :=
  WithLp.toLp 2 (fun k => fderiv ℝ f x (CotangentLogCoframe.H (d F) x
    (EuclideanSpace.basisFun _ ℝ k)))

private theorem orthGradient_pair_transport
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I)
    (L : EuclideanSpace ℝ I →L[ℝ] ℂ) (v : EuclideanSpace ℂ I) :
    inner ℂ (WithLp.toLp 2 (fun k => L (q (EuclideanSpace.basisFun _ ℝ k)))) v =
      inner ℂ (WithLp.toLp 2 (fun k => L (EuclideanSpace.basisFun _ ℝ k)))
        (orthogonalComplexification I q v) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply']
  have hex : ∀ k, L (q (EuclideanSpace.basisFun _ ℝ k)) =
      ∑ l, ((q (EuclideanSpace.basisFun _ ℝ k) l : ℝ) : ℂ) *
        L (EuclideanSpace.basisFun _ ℝ l) := by
    intro k
    conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun _ ℝ)
      (q (EuclideanSpace.basisFun _ ℝ k))]
    simp [EuclideanSpace.basisFun_repr, map_sum, map_smul,
      RCLike.real_smul_eq_coe_mul]
  simp only [hex, map_sum, map_mul, Complex.conj_ofReal]
  have hq : orthogonalComplexification I q v =
      operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap v := by
    rw [← orthogonalComplexification_toContinuousLinearMap]
    rfl
  rw [hq]
  simp only [operatorComplexification_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ((q (EuclideanSpace.basisFun I ℝ j) i : ℝ) : ℂ) *
      starRingEnd ℂ (L (EuclideanSpace.basisFun I ℝ i)) * v j =
      starRingEnd ℂ (L (EuclideanSpace.basisFun I ℝ i)) *
        (((q (EuclideanSpace.basisFun I ℝ j) i : ℝ) : ℂ) * v j)
  ring

private theorem orthGradient_arrow_pair (a : ShrunkChart F ζ hζ U R P H)
    (σ : a.Isotropy) (x : M F) (hx : x ∈ omega a)
    (f : M F → ℂ) (hf : DifferentiableAt ℝ f ((isotropyArrow a (geometricLift a σ)).psi x))
    (W : Family (U := U) (H := H)) :
    inner ℂ (orthGradient (f ∘ (isotropyArrow a (geometricLift a σ)).psi) x)
      (coefficient W a ⟨x,hx⟩) =
      (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ)⁻¹ *
        inner ℂ (orthGradient f ((isotropyArrow a (geometricLift a σ)).psi x))
          (coefficient W a ⟨_, isotropy_mem a (geometricLift a σ) x hx⟩) := by
  let e := isotropyArrow a (geometricLift a σ)
  have hx' : x ∈ e.domain := omega_subset_larger a hx
  have he := ((smooth_metric e).1.differentiableOn (by simp) x hx').differentiableAt
    (e.isOpen_domain.mem_nhds hx')
  have hcov := W.property.2.1 a (geometricLift a σ) x hx
  change coefficient W a ⟨e.psi x, _⟩ = T e x hx' (coefficient W a ⟨x,hx⟩) at hcov
  rw [hcov, T_apply, inner_smul_right]
  rw [geometricLift_phase]
  rw [← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
  have hframe : ∀ v : V F, fderiv ℝ e.psi x (CotangentLogCoframe.H (d F) x v) =
      CotangentLogCoframe.H (d F) (e.psi x) (q e x hx' v) := by
    intro v
    apply (CotangentLogCoframe.C (d F) (e.psi x)).injective
    simp only [CotangentLogCoframe.H, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hgrad : orthGradient (f ∘ e.psi) x =
      WithLp.toLp 2 (fun k =>
        ((fderiv ℝ f (e.psi x)).comp (CotangentLogCoframe.H (d F) (e.psi x)).toContinuousLinearMap)
          (q e x hx' (EuclideanSpace.basisFun _ ℝ k))) := by
    apply PiLp.ext
    intro k
    change fderiv ℝ (f ∘ e.psi) x _ = _
    rw [fderiv_comp x hf he, ContinuousLinearMap.comp_apply, hframe]
    rfl
  rw [hgrad]
  exact orthGradient_pair_transport (q e x hx') _ _

 def flatIndex : Fin (KPCuspLogShape.dimension F * 3) ≃ (Fin (d F) × Fin 3) :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (placeEquiv F ζ hζ).symm (Equiv.refl (Fin 3)))
 def flatMap : Space (KPCuspLogShape.dimension F * 3) ≃ₗᵢ[ℝ] M F :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (flatIndex (F := F) (ζ := ζ) (hζ := hζ))
private theorem flatMap_apply (p : Space (KPCuspLogShape.dimension F * 3)) :
    flatMap (ζ := ζ) (hζ := hζ) p = labeledAInv (placeEquiv F ζ hζ) (coordinates F p) := by
  apply PiLp.ext
  rintro ⟨i,k⟩
  fin_cases k <;> simp [flatMap, flatIndex, labeledAInv, coordinates,
    KPArchRealCoordinates.coordinates, CotangentLogCoframe.A, Equiv.piCongrLeft']
private theorem flatMap_action (a : ShrunkChart F ζ hζ U R P H) (σ : a.Isotropy)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    flatMap (ζ := ζ) (hζ := hζ) (overlapCoordinate F ζ hζ U R P H a.component σ.val p) =
      (isotropyArrow a (geometricLift a σ)).psi (flatMap (ζ := ζ) (hζ := hζ) p) := by
  rw [flatMap_apply, flatMap_apply, geometricLift_psi, labeled_roundtrip]
  simp only [overlapCoordinate, Homeomorph.apply_symm_apply]
private theorem flatMap_single (i : Fin (d F)) (k : Fin 3) :
    (flatMap (ζ := ζ) (hζ := hζ)).symm (EuclideanSpace.single (i,k) 1) =
      EuclideanSpace.single (finProdFinEquiv ((placeEquiv F ζ hζ) i,k)) 1 := by
  ext j
  simp [flatMap, flatIndex, LinearIsometryEquiv.piLpCongrLeft_symm,
    ]
set_option maxHeartbeats 1200000 in
private theorem flatMap_H (p : Space (KPCuspLogShape.dimension F * 3))
    (i : Fin (d F)) (k : Fin 3) :
    (flatMap (ζ := ζ) (hζ := hζ)).symm
      (CotangentLogCoframe.H (d F) (flatMap (ζ := ζ) (hζ := hζ) p)
        (EuclideanSpace.basisFun _ ℝ (i,k))) =
      (if k = 0 then 1 else Real.exp ((coordinates F p ((placeEquiv F ζ hζ) i)).2)) •
        EuclideanSpace.single
          (finProdFinEquiv ((placeEquiv F ζ hζ) i, ![2,0,1] k)) 1 := by
  have hheight : flatMap (ζ := ζ) (hζ := hζ) p (i,2) =
      (coordinates F p ((placeEquiv F ζ hζ) i)).2 := by
    rw [flatMap_apply]
    simp [labeledAInv, CotangentLogCoframe.A]
  have hh : CotangentLogCoframe.H (d F) (flatMap (ζ := ζ) (hζ := hζ) p)
      (EuclideanSpace.basisFun _ ℝ (i,k)) =
      (if k = 0 then 1 else Real.exp ((coordinates F p ((placeEquiv F ζ hζ) i)).2)) •
        EuclideanSpace.single (i, ![2,0,1] k) 1 := by
    fin_cases k <;> ext ⟨l,c⟩ <;> fin_cases c <;>
      simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        EuclideanSpace.basisFun_apply, EuclideanSpace.single, eq_comm]
    all_goals split_ifs <;> simp_all
  rw [hh, map_smul, flatMap_single]

private theorem orthGradient_flat (f : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hf : Differentiable ℝ f) (p : Space (KPCuspLogShape.dimension F * 3))
    (i : Fin (d F)) (k : Fin 3) :
    orthGradient (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm) (flatMap (ζ := ζ) (hζ := hζ) p) (i,k) =
      (if k = 0 then 1 else (Real.exp ((coordinates F p ((placeEquiv F ζ hζ) i)).2) : ℂ)) *
        coordinateDerivativeList [finProdFinEquiv ((placeEquiv F ζ hζ) i, ![2,0,1] k)] f p := by
  change fderiv ℝ (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm)
    (flatMap (ζ := ζ) (hζ := hζ) p) _ = _
  rw [fderiv_comp _ hf.differentiableAt (flatMap (ζ := ζ) (hζ := hζ)).symm.differentiableAt]
  have hd : fderiv ℝ (fun x => (flatMap (ζ := ζ) (hζ := hζ)).symm x)
      (flatMap (ζ := ζ) (hζ := hζ) p) =
      (flatMap (ζ := ζ) (hζ := hζ)).symm.toContinuousLinearEquiv.toContinuousLinearMap :=
    (flatMap (ζ := ζ) (hζ := hζ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  change fderiv ℝ f p ((flatMap (ζ := ζ) (hζ := hζ)).symm _) = _
  rw [flatMap_H, map_smul]
  fin_cases k <;> simp [coordinateDerivativeList, RCLike.real_smul_eq_coe_mul]

 def flatPair (a : ShrunkChart F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (p : Space (KPCuspLogShape.dimension F * 3)) : ℂ :=
  inner ℂ (orthGradient (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm)
    (flatMap (ζ := ζ) (hζ := hζ) p))
    (liftExtension a (coefficient W a) (flatMap (ζ := ζ) (hζ := hζ) p))

private theorem flatPair_action (a : ShrunkChart F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (σ : a.Isotropy) (f : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (p : Space (KPCuspLogShape.dimension F * 3))
    (hp : coordinates F p ∈ a.domain) :
    flatPair a W (f ∘ overlapCoordinate F ζ hζ U R P H a.component σ.val) p =
      (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ)⁻¹ *
        flatPair a W f (overlapCoordinate F ζ hζ U R P H a.component σ.val p) := by
  let L := flatMap (F := F) (ζ := ζ) (hζ := hζ)
  let e := isotropyArrow a (geometricLift a σ)
  have hx : L p ∈ omega a := by
    rw [flatMap_apply]
    change labeledA (placeEquiv F ζ hζ) _ ∈ a.domain
    rwa [labeled_roundtrip]
  have hy : L (overlapCoordinate F ζ hζ U R P H a.component σ.val p) ∈ omega a := by
    rw [flatMap_action]
    exact isotropy_mem a (geometricLift a σ) _ hx
  have hcomp : (f ∘ overlapCoordinate F ζ hζ U R P H a.component σ.val) ∘ L.symm =
      (f ∘ L.symm) ∘ e.psi := by
    funext x
    have he := flatMap_action a σ (L.symm x)
    change L _ = e.psi (L (L.symm x)) at he
    rw [L.apply_symm_apply] at he
    have hh := congrArg L.symm he
    simp only [L.symm_apply_apply] at hh
    exact congrArg f hh
  unfold flatPair
  rw [hcomp]
  have hxL : flatMap (ζ := ζ) (hζ := hζ) p ∈ omega a := hx
  have hyL : flatMap (ζ := ζ) (hζ := hζ)
      (overlapCoordinate F ζ hζ U R P H a.component σ.val p) ∈ omega a := hy
  rw [liftExtension, dite_eq_left hxL, liftExtension, dite_eq_left hyL]
  simp only [flatMap_action]
  exact orthGradient_arrow_pair a σ _ hx _
    ((hf.comp L.symm.contDiff).differentiable (by simp)).differentiableAt W

private theorem orthGradient_project_pair (a : ShrunkChart F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) (x : omega a)
    (f : M F → ℂ) (hf : Differentiable ℝ f) :
    inner ℂ (orthGradient ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection ∘ f) x.val)
      (coefficient W a x) = inner ℂ (orthGradient f x.val) (coefficient W a x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k hk
  change inner ℂ (fderiv ℝ ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection ∘ f) x.val _)
    (coefficient W a x k) = inner ℂ (fderiv ℝ f x.val _) (coefficient W a x k)
  have hc := fderiv_comp x.val
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection.restrictScalars ℝ).differentiableAt
    hf.differentiableAt
  change fderiv ℝ ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection ∘ f) x.val = _ at hc
  rw [hc]
  simp only [ContinuousLinearMap.comp_apply]
  have hd := (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection.restrictScalars ℝ |>.fderiv
    (x := f x.val)
  rw [hd]
  exact Submodule.inner_starProjection_left_eq_right _ _ _ |>.trans
    (by rw [Submodule.starProjection_eq_self_iff.mpr (coefficient_mem_scalarFiber a W x k)])

private theorem flatPair_project (a : ShrunkChart F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (p : Space (KPCuspLogShape.dimension F * 3)) (hp : coordinates F p ∈ a.domain) :
    flatPair a W ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection ∘ f) p =
      flatPair a W f p := by
  have hx : flatMap (ζ := ζ) (hζ := hζ) p ∈ omega a := by
    rw [flatMap_apply]
    change labeledA (placeEquiv F ζ hζ) _ ∈ a.domain
    rwa [labeled_roundtrip]
  unfold flatPair
  rw [liftExtension, dite_eq_left hx]
  exact orthGradient_project_pair a W ⟨_,hx⟩ _
    ((hf.comp (flatMap (ζ := ζ) (hζ := hζ)).symm.contDiff).differentiable (by simp))

private theorem flatPair_const_mul (a : ShrunkChart F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℂ)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    flatPair a W (fun y => c * f y) p = star c * flatPair a W f p := by
  unfold flatPair
  have he : (fun y => c * f y) ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm =
      c • (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm) := rfl
  rw [he]
  have hg : orthGradient (c • (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm))
      (flatMap (ζ := ζ) (hζ := hζ) p) =
      c • orthGradient (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm)
        (flatMap (ζ := ζ) (hζ := hζ) p) := by
    apply PiLp.ext
    intro k
    change fderiv ℝ (c • (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm)) _ _ = _
    rw [fderiv_const_smul ((hf.comp (flatMap (ζ := ζ) (hζ := hζ)).symm.contDiff).differentiable
      (by simp)).differentiableAt]
    rfl
  rw [hg, inner_smul_left]
  rfl

private theorem flatPair_sum {I : Type*} (s : Finset I)
    (a : ShrunkChart F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (f : I → Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hf : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    flatPair a W (fun y => ∑ i ∈ s, f i y) p = ∑ i ∈ s, flatPair a W (f i) p := by
  unfold flatPair
  have hg : orthGradient ((fun y => ∑ i ∈ s, f i y) ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm)
      (flatMap (ζ := ζ) (hζ := hζ) p) =
      ∑ i ∈ s, orthGradient (f i ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm)
        (flatMap (ζ := ζ) (hζ := hζ) p) := by
    apply PiLp.ext
    intro k
    simp only [orthGradient, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_toLp]
    have hsum : ((fun y => ∑ i ∈ s, f i y) ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm) =
        (fun y => ∑ i ∈ s, (f i ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm) y) := rfl
    rw [hsum, fderiv_fun_sum (fun i hi =>
      ((hf i hi).comp (flatMap (ζ := ζ) (hζ := hζ)).symm.contDiff).differentiable (by simp) |>.differentiableAt)]
    simp
  rw [hg, sum_inner]

private theorem overlap_smooth (a : ShrunkChart F ζ hζ U R P H) (σ : a.Isotropy) :
    ContDiff ℝ (⊤ : ℕ∞) (overlapCoordinate F ζ hζ U R P H a.component σ.val) := by
  exact (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_symm_contDiff _).comp
    ((CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F σ.val.val).comp
      (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_contDiff _))

private theorem flatPair_reynolds_term (a : ShrunkChart F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) (σ : a.Isotropy)
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (p : Space (KPCuspLogShape.dimension F * 3)) (hp : coordinates F p ∈ a.domain) :
    flatPair a W (fun y =>
      (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ)⁻¹ *
        (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
          (f (overlapCoordinate F ζ hζ U R P H a.component σ.val y))) p =
      flatPair a W f (overlapCoordinate F ζ hζ U R P H a.component σ.val p) := by
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
        (f (overlapCoordinate F ζ hζ U R P H a.component σ.val y))) := by
    exact ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection.restrictScalars ℝ).contDiff.comp
      (hf.comp (overlap_smooth a σ))
  have hproject : (fun y => (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
      (f (overlapCoordinate F ζ hζ U R P H a.component σ.val y))) =
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection ∘
        (f ∘ overlapCoordinate F ζ hζ U R P H a.component σ.val) := rfl
  rw [flatPair_const_mul a W _
    hproj, hproject, flatPair_project a W _ (hf.comp (overlap_smooth a σ)) p hp,
    flatPair_action a W σ f hf p hp]
  have hc : star (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ)⁻¹ =
      (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ) := by
    rw [← Circle.coe_inv, Complex.star_def, ← Circle.coe_inv_eq_conj, inv_inv]
  rw [hc, ← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul]

private theorem flat_field_memLp (a : ShrunkChart F ζ hζ U R P H)
    (W : SquareFiniteFamily (U := U) (H := H)) :
    MemLp (fun p => liftExtension a (coefficient W.val a) (flatMap (ζ := ζ) (hζ := hζ) p)) 2
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        ((coordinates F) ⁻¹' a.domain)) := by
  let : Finite a.Isotropy := chart_stabilizer_finite F ζ hζ U R P H a.component a.center a.larger
  let c := (H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ℝ≥0∞)
  have hc : c ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    exact ⟨ne_of_gt ((H.disintegration U).positive_componentWeight a.component), ENNReal.natCast_ne_top _⟩
  let μ := (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain
  have hl := KPContActualCotangentChartRestriction.localCoefficient_memLp a W
  change MemLp _ 2 (c • Measure.comap (Subtype.val : a.domain → _) μ) at hl
  have hl' : MemLp (KPContActualCotangentChartRestriction.localCoefficient a W.val) 2
      (Measure.comap (Subtype.val : a.domain → _) μ) := by
    apply hl.of_measure_le_smul (c := c⁻¹) (ENNReal.inv_ne_top.mpr hc)
    rw [← smul_assoc, smul_eq_mul, ENNReal.inv_mul_cancel hc (by
      exact ENNReal.div_ne_top ((H.disintegration U).finite_componentWeight a.component).ne
        (by exact_mod_cast Nat.card_pos.ne' : (Nat.card a.Isotropy : ℝ≥0∞) ≠ 0)), one_smul]
  let g : SymmetricSpace F → E F := fun z =>
    liftExtension a (coefficient W.val a) (labeledAInv (placeEquiv F ζ hζ) z)
  have hg : MemLp g 2 μ := by
    have hs := (MeasurableEmbedding.subtype_coe a.domain_open.measurableSet).memLp_map_measure_iff
      (g := g) (p := (2 : ℝ≥0∞)) (μ := Measure.comap (Subtype.val : a.domain → _) μ)
    rw [map_comap_subtype_coe a.domain_open.measurableSet,
      Measure.restrict_restrict a.domain_open.measurableSet, Set.inter_self] at hs
    apply hs.mpr
    convert hl' using 1
    funext y
    have hx : labeledAInv (placeEquiv F ζ hζ) y.val ∈ omega a := by
      change labeledA (placeEquiv F ζ hζ) _ ∈ a.domain
      rw [labeled_roundtrip]
      exact y.property
    simp only [g, Function.comp_apply, liftExtension, dite_eq_left hx,
      KPContActualCotangentChartRestriction.localCoefficient,
      KPContActualCotangentPieceHilbertSum.coordinates]
  have hmp : MeasurePreserving (coordinates F)
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        ((coordinates F) ⁻¹' a.domain)) μ := by
    refine ⟨(coordinates F).continuous.measurable, ?_⟩
    rw [← Measure.restrict_map (coordinates F).continuous.measurable a.domain_open.measurableSet,
      metric_volume F]
  have h := hg.comp_measurePreserving hmp
  have he : (g ∘ coordinates F) =
      (fun p => liftExtension a (coefficient W.val a) (flatMap (ζ := ζ) (hζ := hζ) p)) := by
    funext p
    simp only [g, Function.comp_apply, flatMap_apply]
  rw [he] at h
  exact h

private theorem weighted_finite_compacts :
    IsFiniteMeasureOnCompacts (volume.withDensity (fun p : Space (KPCuspLogShape.dimension F * 3) =>
      ENNReal.ofReal (density F p))) := by
  constructor
  intro K hK
  rw [withDensity_apply _ hK.measurableSet]
  have hi : IntegrableOn (density F) K volume :=
    ((density_smooth F).continuous.continuousOn).integrableOn_compact hK
  have h := hi.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at h
  apply lt_of_le_of_lt _ h
  apply lintegral_mono
  intro p
  change ENNReal.ofReal (density F p) ≤ ‖density F p‖ₑ
  rw [Real.enorm_eq_ofReal (density_positive F p).le]

private theorem flat_gradient_memLp (a : ShrunkChart F ζ hζ U R P H)
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    MemLp (fun p => orthGradient (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm)
      (flatMap (ζ := ζ) (hζ := hζ) p)) 2
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        ((coordinates F) ⁻¹' a.domain)) := by
  have : IsFiniteMeasureOnCompacts (volume.withDensity
      (fun p : Space (KPCuspLogShape.dimension F * 3) => ENNReal.ofReal (density F p))) := weighted_finite_compacts
  apply Continuous.memLp_of_hasCompactSupport
  · apply (PiLp.continuous_toLp 2 (fun _ : Fin (d F) × Fin 3 => ℂ)).comp
    apply continuous_pi
    rintro ⟨i,k⟩
    have hder := (hf.comp (flatMap (ζ := ζ) (hζ := hζ)).symm.contDiff).continuous_fderiv (by simp)
    exact (hder.comp (flatMap (ζ := ζ) (hζ := hζ)).continuous).clm_apply
      (((CotangentLogCoframe.contDiff_H (d F)).continuous.comp
        (flatMap (ζ := ζ) (hζ := hζ)).continuous).clm_apply continuous_const)
  · have hs : tsupport (fun p => orthGradient (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm)
        (flatMap (ζ := ζ) (hζ := hζ) p)) ⊆ tsupport f := by
      apply closure_minimal _ (isClosed_tsupport f)
      intro p hp
      by_contra hn
      apply hp
      apply PiLp.ext
      rintro ⟨i,k⟩
      rw [orthGradient_flat f (hf.differentiable (by simp))]
      change _ * fderiv ℝ f p _ = 0
      rw [fderiv_of_notMem_tsupport ℝ hn]
      simp
    exact hfc.of_isClosed_subset isClosed_closure hs

private theorem flatPair_integrable (a : ShrunkChart F ζ hζ U R P H)
    (W : SquareFiniteFamily (U := U) (H := H))
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    Integrable (flatPair a W.val f)
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        ((coordinates F) ⁻¹' a.domain)) :=
  KPTestL2.integrable_pairing _ _ _ (flat_gradient_memLp a f hf hfc) (flat_field_memLp a W)

private theorem flatPair_reynolds (a : ShrunkChart F ζ hζ U R P H)
    (W : SquareFiniteFamily (U := U) (H := H))
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    [Fintype a.Isotropy] :
    (∫ p in (coordinates F) ⁻¹' a.domain,
      flatPair a W.val (fun y => (Nat.card a.Isotropy : ℂ)⁻¹ * ∑ σ : a.Isotropy,
        (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ)⁻¹ *
          (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
            (f (overlapCoordinate F ζ hζ U R P H a.component σ.val y))) p
      ∂volume.withDensity (fun p => ENNReal.ofReal (density F p))) =
      ∫ p in (coordinates F) ⁻¹' a.domain, flatPair a W.val f p
        ∂volume.withDensity (fun p => ENNReal.ofReal (density F p)) := by
  let t := fun σ : a.Isotropy => fun y : Space (KPCuspLogShape.dimension F * 3) =>
    (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ)⁻¹ *
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
        (f (overlapCoordinate F ζ hζ U R P H a.component σ.val y))
  have ht : ∀ σ, ContDiff ℝ (⊤ : ℕ∞) (t σ) := by
    intro σ
    exact contDiff_const.mul
      (((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection.restrictScalars ℝ).contDiff.comp
        (hf.comp (overlap_smooth a σ)))
  have he : ∀ σ, (∫ p in (coordinates F) ⁻¹' a.domain, flatPair a W.val (t σ) p
      ∂volume.withDensity (fun p => ENNReal.ofReal (density F p))) =
      ∫ p in (coordinates F) ⁻¹' a.domain, flatPair a W.val f p
        ∂volume.withDensity (fun p => ENNReal.ofReal (density F p)) := by
    intro σ
    rw [integral_congr_ae (show flatPair a W.val (t σ) =ᵐ[
      (volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict ((coordinates F) ⁻¹' a.domain)]
      (flatPair a W.val f ∘ overlapCoordinate F ζ hζ U R P H a.component σ.val) from by
        filter_upwards [ae_restrict_mem ((coordinates F).continuous.measurable a.domain_open.measurableSet)] with p hp
        exact flatPair_reynolds_term a W.val σ f hf p hp)]
    let : ContinuousConstSMul (KPCuspArithmetic.PGL2 F) (SymmetricSpace F) := ⟨KPCuspSiegel.continuous_action F⟩
    exact (geometric_preserving a σ).integral_comp
      (((coordinates F).trans (Homeomorph.smul σ.val.val)).trans (coordinates F).symm).measurableEmbedding _
  have hi : ∀ σ, Integrable (flatPair a W.val (t σ))
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict ((coordinates F) ⁻¹' a.domain)) := by
    intro σ
    have hi' := flatPair_integrable a W f hf hfc
    rw [← (geometric_preserving a σ).map_eq] at hi'
    have htcomp := hi'.comp_measurable (geometric_preserving a σ).measurable
    apply htcomp.congr
    filter_upwards [ae_restrict_mem ((coordinates F).continuous.measurable a.domain_open.measurableSet)] with p hp
    exact (flatPair_reynolds_term a W.val σ f hf p hp).symm
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ σ, t σ y) := ContDiff.sum (fun σ _ => ht σ)
  change (∫ p in (coordinates F) ⁻¹' a.domain,
    flatPair a W.val (fun y => (Nat.card a.Isotropy : ℂ)⁻¹ * ∑ σ, t σ y) p
    ∂volume.withDensity (fun p => ENNReal.ofReal (density F p))) = _
  simp_rw [flatPair_const_mul a W.val _ hsm]
  have hsum : (fun p => flatPair a W.val (fun y => ∑ σ, t σ y) p) =
      (fun p => ∑ σ, flatPair a W.val (t σ) p) := by
    funext p
    exact flatPair_sum Finset.univ a W.val t (fun σ _ => ht σ) p
  rw [integral_const_mul, hsum, integral_finsetSum _ (fun σ _ => hi σ)]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hr : star (Fintype.card a.Isotropy : ℂ)⁻¹ = (Fintype.card a.Isotropy : ℂ)⁻¹ := by simp
  rw [hr, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_pos.ne'), one_mul]

 def decoded (p : Space (KPCuspLogShape.dimension F * 3)) (v : E F)
    (j : Fin (KPCuspLogShape.dimension F * 3)) : ℂ :=
  let ik := finProdFinEquiv.symm j
  let q := labeledAInv (placeEquiv F ζ hζ) (coordinates F p)
  let k := (placeEquiv F ζ hζ).symm ik.1
  ![(Real.exp (-q (k, 2)) : ℂ) * v (k, 1),
    (Real.exp (-q (k, 2)) : ℂ) * v (k, 2), v (k, 0)] ik.2
 def coordinatePair (a : ShrunkChart F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (p : Space (KPCuspLogShape.dimension F * 3)) : ℂ :=
  ∑ j : Fin (KPCuspLogShape.dimension F * 3),
    (((if (finProdFinEquiv.symm j).2 = 2 then 1 else
      Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℝ) : ℂ) *
      decoded (ζ := ζ) (hζ := hζ) p
        (liftExtension a (coefficient W a) (flatMap (ζ := ζ) (hζ := hζ) p)) j *
        star (coordinateDerivativeList [j] f p)

private theorem coordinatePair_eq (a : ShrunkChart F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    coordinatePair a W f p = flatPair a W f p := by
  unfold coordinatePair flatPair
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [← Equiv.sum_comp (placeEquiv F ζ hζ), PiLp.inner_apply]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  have hheight : labeledAInv (placeEquiv F ζ hζ) (coordinates F p) (i,2) =
      (coordinates F p ((placeEquiv F ζ hζ) i)).2 := by simp [labeledAInv, CotangentLogCoframe.A]
  simp only [Fin.sum_univ_three, decoded, Equiv.symm_apply_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, hheight,
    orthGradient_flat f (hf.differentiable (by simp)), RCLike.inner_apply']
  dsimp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    ite_false, ite_true, map_mul, Complex.ofReal_one, Complex.conj_ofReal,
    map_one, Complex.star_def]
  have hex : (Real.exp (2 * (coordinates F p ((placeEquiv F ζ hζ) i)).2) : ℂ) *
      (Real.exp (-(coordinates F p ((placeEquiv F ζ hζ) i)).2) : ℂ) =
      (Real.exp ((coordinates F p ((placeEquiv F ζ hζ) i)).2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  calc
    _ = ((Real.exp (2 * (coordinates F p ((placeEquiv F ζ hζ) i)).2) : ℂ) *
      (Real.exp (-(coordinates F p ((placeEquiv F ζ hζ) i)).2) : ℂ)) *
      ((liftExtension a (coefficient W a) (flatMap (ζ := ζ) (hζ := hζ) p)) (i,1) *
        starRingEnd ℂ (coordinateDerivativeList [finProdFinEquiv ((placeEquiv F ζ hζ) i,0)] f p) +
       (liftExtension a (coefficient W a) (flatMap (ζ := ζ) (hζ := hζ) p)) (i,2) *
        starRingEnd ℂ (coordinateDerivativeList [finProdFinEquiv ((placeEquiv F ζ hζ) i,1)] f p)) +
      (liftExtension a (coefficient W a) (flatMap (ζ := ζ) (hζ := hζ) p)) (i,0) *
        starRingEnd ℂ (coordinateDerivativeList [finProdFinEquiv ((placeEquiv F ζ hζ) i,2)] f p) := by ring
    _ = _ := by rw [hex]; ring

private theorem flatPair_zero (a : ShrunkChart F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) (f : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (p : Space (KPCuspLogShape.dimension F * 3))
    (hp : p ∉ tsupport f) : flatPair a W f p = 0 := by
  unfold flatPair
  have hz : orthGradient (f ∘ (flatMap (ζ := ζ) (hζ := hζ)).symm)
      (flatMap (ζ := ζ) (hζ := hζ) p) = 0 := by
    apply PiLp.ext
    rintro ⟨i,k⟩
    rw [orthGradient_flat f (hf.differentiable (by simp))]
    change _ * fderiv ℝ f p _ = 0
    rw [fderiv_of_notMem_tsupport ℝ hp]
    simp
  rw [hz, inner_zero_left]

private theorem weighted_integral (a : ShrunkChart F ζ hζ U R P H)
    (f : Space (KPCuspLogShape.dimension F * 3) → ℂ) :
    (∫ p in (coordinates F) ⁻¹' a.domain, f p
      ∂volume.withDensity (fun p => ENNReal.ofReal (density F p))) =
      ∫ p in (coordinates F) ⁻¹' a.domain, (density F p : ℂ) * f p := by
  have hd := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (μ := volume) (f := fun p => ENNReal.ofReal (density F p))
    (ENNReal.measurable_ofReal.comp (density_smooth F).continuous.measurable).aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f
    ((coordinates F).continuous.measurable a.domain_open.measurableSet)
  simp only [ENNReal.toReal_ofReal (density_positive F _).le, RCLike.real_smul_eq_coe_mul] at hd
  exact hd

theorem tensor_reynolds_integral
    (a : ShrunkChart F ζ hζ U R P H)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : coordinates F '' KPContLocalCubeEmbedding.closedCarrier A ⊆ a.domain)
    (ε : rootsOfUnity 3 F) (W : SquareFiniteFamily (U := U) (H := H))
    (φ : TestFunction A.toOpens ℂ ⊤) :
    letI : Finite a.Isotropy := chart_stabilizer_finite F ζ hζ U R P H
      a.component a.center a.larger
    letI : Fintype a.Isotropy := Fintype.ofFinite a.Isotropy
    let ψ : Space (KPCuspLogShape.dimension F * 3) → ℂ := fun p =>
      (Nat.card a.Isotropy : ℂ)⁻¹ * ∑ σ : a.Isotropy,
        (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ)⁻¹ *
          (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
            (φ (overlapCoordinate F ζ hζ U R P H a.component σ.val p))
    let b : Space (KPCuspLogShape.dimension F * 3) → Fin (KPCuspLogShape.dimension F * 3) → ℂ :=
      fun p j =>
        let ik := finProdFinEquiv.symm j
        let q := labeledAInv (placeEquiv F ζ hζ) (coordinates F p)
        let k := (placeEquiv F ζ hζ).symm ik.1
        let v := liftExtension a (coefficient W.val a) q
        (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
          ![(Real.exp (-q (k, 2)) : ℂ) * v (k, 1),
            (Real.exp (-q (k, 2)) : ℂ) * v (k, 2), v (k, 0)] ik.2
    (∫ p in (coordinates F) ⁻¹' a.domain, (density F p : ℂ) *
      ∑ j : Fin (KPCuspLogShape.dimension F * 3),
        (((if (finProdFinEquiv.symm j).2 = 2 then 1 else
          Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℝ) : ℂ) *
          b p j * star (coordinateDerivativeList [j] ψ p)) =
    ∫ p in A.carrier, (density F p : ℂ) *
      ∑ j : Fin (KPCuspLogShape.dimension F * 3),
        (((if (finProdFinEquiv.symm j).2 = 2 then 1 else
          Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℝ) : ℂ) *
          b p j * star (coordinateDerivativeList [j] (fun q => φ q) p) := by
  dsimp only
  let : Finite a.Isotropy := chart_stabilizer_finite F ζ hζ U R P H a.component a.center a.larger
  let : Fintype a.Isotropy := Fintype.ofFinite a.Isotropy
  let ψ : Space (KPCuspLogShape.dimension F * 3) → ℂ := fun p =>
    (Nat.card a.Isotropy : ℂ)⁻¹ * ∑ σ : a.Isotropy,
      (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ)⁻¹ *
        (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
          (φ (overlapCoordinate F ζ hζ U R P H a.component σ.val p))
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply contDiff_const.mul
    apply ContDiff.sum
    intro σ hσ
    exact contDiff_const.mul
      (((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection.restrictScalars ℝ).contDiff.comp
        (φ.contDiff.comp (overlap_smooth a σ)))
  have he := flatPair_reynolds a W (fun p => φ p) φ.contDiff φ.hasCompactSupport
  rw [weighted_integral a, weighted_integral a] at he
  have hAB : A.carrier ⊆ (coordinates F) ⁻¹' a.domain := by
    intro p hp
    exact hA ⟨p, Metric.ball_subset_closedBall hp, rfl⟩
  have hc : (∫ p in (coordinates F) ⁻¹' a.domain,
      (density F p : ℂ) * flatPair a W.val (fun q => φ q) p) =
      ∫ p in A.carrier, (density F p : ℂ) * flatPair a W.val (fun q => φ q) p := by
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      ((coordinates F).continuous.measurable a.domain_open.measurableSet).nullMeasurableSet hAB
    filter_upwards with p hp
    rw [flatPair_zero a W.val _ φ.contDiff p (fun ht => hp.2 (φ.tsupport_subset ht)), mul_zero]
  rw [hc] at he
  change (∫ p in (coordinates F) ⁻¹' a.domain,
    (density F p : ℂ) * ∑ j,
      (((if (finProdFinEquiv.symm j).2 = 2 then 1 else
        Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℝ) : ℂ) *
        ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
          decoded (ζ := ζ) (hζ := hζ) p
            (liftExtension a (coefficient W.val a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) j) *
          star (coordinateDerivativeList [j] ψ p)) = _
  have hfactor : ∀ (f : Space (KPCuspLogShape.dimension F * 3) → ℂ) p,
      (∑ j, (((if (finProdFinEquiv.symm j).2 = 2 then 1 else
        Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℝ) : ℂ) *
        ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
          decoded (ζ := ζ) (hζ := hζ) p
            (liftExtension a (coefficient W.val a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) j) *
          star (coordinateDerivativeList [j] f p)) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * coordinatePair a W.val f p := by
    intro f p
    unfold coordinatePair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [flatMap_apply]
    ring
  change (∫ p in (coordinates F) ⁻¹' a.domain,
    (density F p : ℂ) * ∑ j,
      (((if (finProdFinEquiv.symm j).2 = 2 then 1 else
        Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℝ) : ℂ) *
        ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * decoded (ζ := ζ) (hζ := hζ) p
          (liftExtension a (coefficient W.val a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) j) *
          star (coordinateDerivativeList [j] ψ p)) =
    ∫ p in A.carrier, (density F p : ℂ) * ∑ j,
      (((if (finProdFinEquiv.symm j).2 = 2 then 1 else
        Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℝ) : ℂ) *
        ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * decoded (ζ := ζ) (hζ := hζ) p
          (liftExtension a (coefficient W.val a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) j) *
          star (coordinateDerivativeList [j] (fun q => φ q) p)
  simp_rw [hfactor]
  have hleft : (fun p => (density F p : ℂ) *
      ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * coordinatePair a W.val ψ p)) =
      (fun p => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        ((density F p : ℂ) * flatPair a W.val ψ p)) := by
    funext p
    rw [coordinatePair_eq a W.val ψ hψ]
    ring
  have hright : (fun p => (density F p : ℂ) *
      ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * coordinatePair a W.val (fun q => φ q) p)) =
      (fun p => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        ((density F p : ℂ) * flatPair a W.val (fun q => φ q) p)) := by
    funext p
    rw [coordinatePair_eq a W.val _ φ.contDiff]
    ring
  rw [hleft, hright, integral_const_mul, integral_const_mul]
  exact congrArg ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * ·) he

end DedekindZetaZeroFree.KPContFriedrichsTensorReynolds

end
