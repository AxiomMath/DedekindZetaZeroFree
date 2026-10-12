module

public import DedekindZetaZeroFree.Adeles.Quotients.LineSections.ChartRestrictionDensity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.WeakGradientLocalization
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.LocalH1EnergyEstimates

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContFriedrichsWeakGradientCoordinates

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 def permIsometry {n m : ℕ} (e : Fin n ≃ Fin m) : Space n ≃ₗᵢ[ℝ] Space m :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

 def permBall {n m : ℕ} (e : Fin n ≃ Fin m) (B : LocalBall n) : LocalBall m :=
  ⟨by
    have h : n = m := by simpa using Fintype.card_congr e
    exact h ▸ B.dimension_pos,
   permIsometry e B.center, B.radius, B.radius_pos⟩

private theorem permBall_preimage {n m : ℕ} (e : Fin n ≃ Fin m) (B : LocalBall n) :
    permIsometry e ⁻¹' (permBall e B).carrier = B.carrier := by
  ext x
  change dist (permIsometry e x) (permIsometry e B.center) < B.radius ↔ _
  rw [(permIsometry e).dist_map]
  rfl

private theorem perm_preserving {n m : ℕ} (e : Fin n ≃ Fin m) (B : LocalBall n) :
    MeasurePreserving (permIsometry e) (volume.restrict B.carrier)
      (volume.restrict (permBall e B).carrier) := by
  have h := (permIsometry e).measurePreserving.restrict_preimage_emb
    (permIsometry e).toHomeomorph.measurableEmbedding (permBall e B).carrier
  rwa [permBall_preimage] at h

private theorem perm_single {n m : ℕ} (e : Fin n ≃ Fin m) (j : Fin n) :
    permIsometry e (EuclideanSpace.single j 1) = EuclideanSpace.single (e j) 1 := by
  ext k
  simp only [permIsometry, LinearIsometryEquiv.piLpCongrLeft_apply]
  simp [Pi.single_apply, Equiv.symm_apply_eq]

 def permTest {n m : ℕ} (e : Fin n ≃ Fin m) (B : LocalBall n)
    (φ : TestFunction B.toOpens ℂ ⊤) : TestFunction (permBall e B).toOpens ℂ ⊤ :=
  ⟨fun x => φ ((permIsometry e).symm x),
    φ.contDiff.comp (permIsometry e).symm.contDiff,
    by
      exact φ.hasCompactSupport.comp_homeomorph (permIsometry e).symm.toHomeomorph,
    by
      have hs := tsupport_comp_eq_preimage (fun x => φ x) (permIsometry e).symm.toHomeomorph
      change tsupport (fun x => φ ((permIsometry e).symm x)) = _ at hs
      rw [hs]
      intro x hx
      have h := φ.tsupport_subset hx
      change dist x (permIsometry e B.center) < B.radius
      have he := (permIsometry e).dist_map ((permIsometry e).symm x) B.center
      rw [(permIsometry e).apply_symm_apply] at he
      rwa [he]⟩

private theorem permTest_deriv {n m : ℕ} (e : Fin n ≃ Fin m) (B : LocalBall n)
    (φ : TestFunction B.toOpens ℂ ⊤) (j : Fin n) (x : Space n) :
    coordinateDerivativeList [e j] (permTest e B φ) (permIsometry e x) =
      coordinateDerivativeList [j] φ x := by
  change fderiv ℝ (fun y => φ ((permIsometry e).symm y)) (permIsometry e x)
    (EuclideanSpace.single (e j) 1) = _
  have hc := fderiv_comp (permIsometry e x)
    (f := fun y => (permIsometry e).symm y) (g := fun y => φ y)
    ((φ.contDiff.differentiable (by simp)).differentiableAt)
    (permIsometry e).symm.differentiableAt
  change fderiv ℝ (fun y => φ ((permIsometry e).symm y)) (permIsometry e x) = _ at hc
  rw [hc]
  simp only [ContinuousLinearMap.comp_apply, (permIsometry e).symm_apply_apply]
  have hd : fderiv ℝ (fun y => (permIsometry e).symm y) (permIsometry e x) =
      (permIsometry e).symm.toContinuousLinearEquiv.toContinuousLinearMap :=
    (permIsometry e).symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv
  rw [hd]
  change fderiv ℝ (fun y => φ y) x ((permIsometry e).symm
    (EuclideanSpace.single (e j) 1)) = _
  have hs : (permIsometry e).symm (EuclideanSpace.single (e j) 1) =
      EuclideanSpace.single j 1 := by
    have h := perm_single e.symm (e j)
    simpa only [permIsometry, LinearIsometryEquiv.piLpCongrLeft_symm,
      Equiv.symm_apply_apply] using h
  rw [hs]
  rfl

private theorem first_dirs {n : ℕ} (j : Fin n) :
    (KPContLocalEnergy.firstIndex j).directions = [j] :=
  KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions j

private theorem first_degree {n : ℕ} (j : Fin n) :
    (KPContLocalEnergy.firstIndex j).degree = 1 := by
  simp only [KPContLocalEnergy.firstIndex, MultiIndex.degree,
    apply_ite Fin.val, Fin.val_one, Fin.val_zero]
  simp

private theorem pull_weak_first {n m : ℕ} (e : Fin n ≃ Fin m) (B : LocalBall n)
    (h : IntegerSobolev (permBall e B) 1) (j : Fin n) :
    IsWeakDerivative B (KPContLocalEnergy.firstIndex j)
      (Lp.compMeasurePreserving (permIsometry e) (perm_preserving e B) (KPContLocalEnergy.value h))
      (Lp.compMeasurePreserving (permIsometry e) (perm_preserving e B)
        (KPContLocalEnergy.gradient h (e j))) := by
  intro φ
  have hw := h.weak_derivatives (KPContLocalEnergy.firstIndex (e j)) (permTest e B φ)
  change (∫ x in (permBall e B).carrier, KPContLocalEnergy.value h x *
    coordinateDerivative (KPContLocalEnergy.firstIndex (e j)) (permTest e B φ) x) =
    (-1 : ℂ) ^ _ * (∫ x in (permBall e B).carrier,
      KPContLocalEnergy.gradient h (e j) x * permTest e B φ x) at hw
  simp only [coordinateDerivative, first_dirs, first_degree] at hw ⊢
  have ht : ∀ x, permTest e B φ (permIsometry e x) = φ x := by
    intro x
    exact congrArg φ ((permIsometry e).symm_apply_apply x)
  rw [← (perm_preserving e B).integral_comp
    (permIsometry e).toHomeomorph.measurableEmbedding
    (fun x => KPContLocalEnergy.value h x * coordinateDerivativeList [e j] (permTest e B φ) x),
    ← (perm_preserving e B).integral_comp
    (permIsometry e).toHomeomorph.measurableEmbedding
    (fun x => KPContLocalEnergy.gradient h (e j) x * permTest e B φ x)] at hw
  simp only [permTest_deriv, ht] at hw
  calc
    _ = ∫ x in B.carrier, KPContLocalEnergy.value h (permIsometry e x) *
        coordinateDerivativeList [j] φ x := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving (KPContLocalEnergy.value h)
        (perm_preserving e B)] with x hx
      rw [hx]
      rfl
    _ = _ := hw
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving (KPContLocalEnergy.gradient h (e j))
        (perm_preserving e B)] with x hx
      rw [hx]
      rfl

private theorem ballLp_locallyIntegrable {n : ℕ} (B : LocalBall n) (u : BallL2 B) :
    LocallyIntegrableOn u B.carrier (volume.restrict B.carrier) := by
  apply (locallyIntegrableOn_iff (μ := volume.restrict B.carrier)
    (f := (fun x => u x)) (s := B.carrier) B.toOpens.isOpen.isLocallyClosed).2
  intro K hK hKc
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hKc.measure_ne_top
  change Integrable _ ((volume.restrict B.carrier).restrict K)
  rw [Measure.restrict_restrict hKc.measurableSet, Set.inter_eq_left.mpr hK]
  exact ((Lp.memLp u).mono_measure (Measure.restrict_mono hK le_rfl)).integrable (by norm_num)

private theorem weakDerivative_unique {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u₁ u₂ d₁ d₂ : BallL2 B)
    (hu : u₁ =ᵐ[volume.restrict B.carrier] u₂)
    (h₁ : IsWeakDerivative B α u₁ d₁) (h₂ : IsWeakDerivative B α u₂ d₂) : d₁ = d₂ := by
  have hi₁ := ballLp_locallyIntegrable B d₁
  have hi₂ := ballLp_locallyIntegrable B d₂
  have hz : ∀ᵐ x ∂volume.restrict B.carrier, x ∈ B.carrier → d₁ x - d₂ x = 0 := by
    apply Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hi₁.sub hi₂)
    intro φ hφ hφc hφs
    have hcast : ContDiff ℝ ∞ (fun x => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    have hsupp : tsupport (fun x => (φ x : ℂ)) = tsupport φ := by
      unfold tsupport
      congr 1
      ext x
      simp
    let ψ : TestFunction B.toOpens ℂ ⊤ :=
      ⟨fun x => (φ x : ℂ), hcast, by change IsCompact _; rw [hsupp]; exact hφc,
        hsupp ▸ hφs⟩
    let ψR : TestFunction B.toOpens ℝ ⊤ := ⟨φ, hφ, hφc, hφs⟩
    have heq : (∫ x in B.carrier, d₁ x * ψ x) = ∫ x in B.carrier, d₂ x * ψ x := by
      apply mul_left_cancel₀ (pow_ne_zero α.degree (by norm_num : (-1 : ℂ) ≠ 0))
      rw [← h₁ ψ, ← h₂ ψ]
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]
    have heq' : (∫ x in B.carrier, φ x • d₁ x) = ∫ x in B.carrier, φ x • d₂ x := by
      simpa only [show (fun x => ψ x) = (fun x => (φ x : ℂ)) from rfl,
        Complex.real_smul, mul_comm] using heq
    change (∫ x in B.carrier, ψR x • (d₁ x - d₂ x)) = 0
    simp only [smul_sub]
    rw [integral_sub (ψR.integrable_smul hi₁) (ψR.integrable_smul hi₂)]
    change (∫ x in B.carrier, φ x • d₁ x) - (∫ x in B.carrier, φ x • d₂ x) = 0
    rw [heq', sub_self]
  apply Lp.ext
  filter_upwards [hz, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
  exact sub_eq_zero.mp (hx hxB)

open KPContActualSectorFormWeakLocalization KPContActualCotangentChartRestriction
open KPContActualSectorChartEquivariantInputs
open KPContCotangentActualOverlap

 def coordinateIndex : Fin (KPCuspLogShape.dimension F * 3) ≃ Fin (3 * d F) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (placeEquiv F ζ hζ).symm (Equiv.refl (Fin 3))).trans coefficientIndex)

private theorem coordinateIndex_inverse (ik : Fin (d F) × Fin 3) :
    (coordinateIndex (F := F) (ζ := ζ) (hζ := hζ)).symm (coefficientIndex ik) =
      finProdFinEquiv ((placeEquiv F ζ hζ) ik.1, ik.2) := by
  change finProdFinEquiv
    ((Equiv.prodCongr (placeEquiv F ζ hζ).symm (Equiv.refl (Fin 3))).symm
      (coefficientIndex.symm (coefficientIndex ik))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem coordinate_compat (p : Space (KPCuspLogShape.dimension F * 3)) :
    (baseReindex (F := F)).symm
      (permIsometry (coordinateIndex (F := F) (ζ := ζ) (hζ := hζ)) p) =
      labeledAInv (placeEquiv F ζ hζ) (coordinates F p) := by
  apply PiLp.ext
  intro ik
  have hleft : ((baseReindex (F := F)).symm
      (permIsometry (coordinateIndex (F := F) (ζ := ζ) (hζ := hζ)) p)) ik =
        p (finProdFinEquiv ((placeEquiv F ζ hζ) ik.1, ik.2)) := by
    simp only [baseReindex, LinearIsometryEquiv.piLpCongrLeft_symm,
      LinearIsometryEquiv.piLpCongrLeft_apply, permIsometry]
    change p ((coordinateIndex (F := F) (ζ := ζ) (hζ := hζ)).symm
      (coefficientIndex ik)) = _
    rw [coordinateIndex_inverse]
  rw [hleft]
  obtain ⟨i,k⟩ := ik
  fin_cases k <;> simp [labeledAInv, coordinates, KPArchRealCoordinates.coordinates,
    CotangentLogCoframe.A]

private theorem labeled_inverse (x : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) x) = x := by
  funext k
  simp [labeledAInv, labeledA]

private theorem coord_ball_inside (a : ShrunkChart F ζ hζ U R P H)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : coordinates F '' KPContLocalCubeEmbedding.closedCarrier A ⊆ a.domain) :
    InteriorBall a (permBall (coordinateIndex (F := F) (ζ := ζ) (hζ := hζ)) A) := by
  let e := coordinateIndex (F := F) (ζ := ζ) (hζ := hζ)
  constructor
  · change IsCompact (closure (Metric.ball (permIsometry e A.center) A.radius))
    rw [closure_ball _ (ne_of_gt A.radius_pos)]
    exact isCompact_closedBall _ _
  · intro x hx
    let p := (permIsometry e).symm x
    have hp : p ∈ KPContLocalCubeEmbedding.closedCarrier A := by
      change x ∈ closure (Metric.ball (permIsometry e A.center) A.radius) at hx
      rw [closure_ball _ (ne_of_gt A.radius_pos)] at hx
      change dist p A.center ≤ A.radius
      have he := (permIsometry e).dist_map p A.center
      change dist ((permIsometry e) ((permIsometry e).symm x)) _ = _ at he
      rw [(permIsometry e).apply_symm_apply] at he
      rwa [← he]
    have hcoord := coordinate_compat (F := F) (ζ := ζ) (hζ := hζ) p
    change (baseReindex (F := F)).symm ((permIsometry e) ((permIsometry e).symm x)) = _ at hcoord
    rw [(permIsometry e).apply_symm_apply] at hcoord
    change labeledA (placeEquiv F ζ hζ) ((baseReindex (F := F)).symm x) ∈ a.domain
    rw [hcoord, labeled_inverse]
    exact hA ⟨p, hp, rfl⟩

private theorem sectionFields_apply (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  have hcoe : (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).kind.representative •
            labeledA (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).places x.val) :=
    rfl
  rw [sectionFields, hcoe]
  simp [KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

theorem coordinate_weak_gradient_decode (s : BorelL2Sections F ζ hζ U R P H)
    (W : Family (U := U) (H := H))
    (hsW : KPContActualSectorFormWeakLocalization.WeakChartData s W)
    (a : ShrunkChart F ζ hζ U R P H)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : coordinates F '' KPContLocalCubeEmbedding.closedCarrier A ⊆ a.domain)
    (ε : rootsOfUnity 3 F) (ξ : IntegerSobolev A 1)
    (hξ : (fun p => KPContLocalEnergy.value ξ p) =ᵐ[volume.restrict A.carrier]
      (fun p => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        (s.val a.component).val (coordinates F p))) :
    ∀ j : Fin (KPCuspLogShape.dimension F * 3),
      (fun p => KPContLocalEnergy.gradient ξ j p) =ᵐ[volume.restrict A.carrier]
      (fun p =>
        let ik := finProdFinEquiv.symm j
        let q := labeledAInv (placeEquiv F ζ hζ) (coordinates F p)
        let k := (placeEquiv F ζ hζ).symm ik.1
        let v := liftExtension a (coefficient W a) q
        (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
          ![(Real.exp (-q (k, 2)) : ℂ) * v (k, 1),
            (Real.exp (-q (k, 2)) : ℂ) * v (k, 2), v (k, 0)] ik.2) := by
  let e := coordinateIndex (F := F) (ζ := ζ) (hζ := hζ)
  let B := permBall e A
  have hB : InteriorBall a B := coord_ball_inside a A hA
  obtain ⟨h, h0, hgrad⟩ := hsW a B hB ε
  have hmp := perm_preserving e A
  have h0pull := hmp.quasiMeasurePreserving.ae_eq_comp h0
  have hu : (Lp.compMeasurePreserving (permIsometry e) hmp (KPContLocalEnergy.value h) : BallL2 A)
      =ᵐ[volume.restrict A.carrier]
        (fun p => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
          (s.val a.component).val (coordinates F p)) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (KPContLocalEnergy.value h) hmp,
      h0pull, ae_restrict_mem A.toOpens.isOpen.measurableSet] with p hp hrep hpA
    rw [hp]
    change KPContLocalEnergy.value h (permIsometry e p) = _
    change KPContLocalEnergy.value h (permIsometry e p) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * scalarCoordinate s a (permIsometry e p) at hrep
    rw [hrep]
    congr 1
    have hdom : coordinates F p ∈ a.domain :=
      hA ⟨p, Metric.ball_subset_closedBall hpA, rfl⟩
    have hq : labeledAInv (placeEquiv F ζ hζ) (coordinates F p) ∈ omega a := by
      change labeledA (placeEquiv F ζ hζ) _ ∈ a.domain
      rwa [labeled_inverse]
    simp only [scalarCoordinate]
    rw [show (baseReindex (F := F)).symm (permIsometry e p) =
      labeledAInv (placeEquiv F ζ hζ) (coordinates F p) from coordinate_compat p]
    rw [liftExtension, dite_eq_left hq, sectionFields_apply, labeled_inverse]
  intro j
  have hj : ((KPContLocalEnergy.firstIndex (e j)).val (e j)).val = 1 := by
    simp [KPContLocalEnergy.firstIndex]
  have hg := hgrad (KPContLocalEnergy.firstIndex (e j)) (e j) hj
  have hgpull := hmp.quasiMeasurePreserving.ae_eq_comp hg
  have heq := weakDerivative_unique A (KPContLocalEnergy.firstIndex j)
    (KPContLocalEnergy.value ξ)
    (Lp.compMeasurePreserving (permIsometry e) hmp (KPContLocalEnergy.value h))
    (KPContLocalEnergy.gradient ξ j)
    (Lp.compMeasurePreserving (permIsometry e) hmp (KPContLocalEnergy.gradient h (e j)))
    (hξ.trans hu.symm) (ξ.weak_derivatives _) (pull_weak_first e A h j)
  have hidx : coefficientIndex.symm (e j) =
      ((placeEquiv F ζ hζ).symm (finProdFinEquiv.symm j).1,
        (finProdFinEquiv.symm j).2) := by
    change coefficientIndex.symm (coefficientIndex _) = _
    rw [Equiv.symm_apply_apply]
    rfl
  filter_upwards [Lp.coeFn_compMeasurePreserving (KPContLocalEnergy.gradient h (e j)) hmp,
    hgpull] with p hp hgp
  rw [heq, hp]
  change KPContLocalEnergy.gradient h (e j) (permIsometry e p) = _ at hgp
  simp only [Function.comp_apply] at hgp ⊢
  rw [hgp]
  simp only [covariantCoordinate, hidx]
  rw [show (baseReindex (F := F)).symm (permIsometry e p) =
    labeledAInv (placeEquiv F ζ hζ) (coordinates F p) from coordinate_compat p]

end DedekindZetaZeroFree.KPContFriedrichsWeakGradientCoordinates

end
