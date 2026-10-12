module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ParameterizedArchimedeanJets

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology Matrix.Norms.Elementwise
open NumberField Filter Set Topology
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalComplexSmoothAction.TranslatedGenerators.NativeApproximation
open KPSpatialSmoothing.ArchKernel hiding G
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming matrixClass → matrixClass
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming matrixDomain → matrixDomain
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming matrixDomain_open → matrixDomain_open
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming matrixClass_mul → matrixClass_mul
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming matrix_pullback_smooth → matrix_pullback_smooth
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming joint_spatial_jets_on → joint_spatial_jets_on
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming localMatrixLift → localMatrixLift
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming localMatrixLift_continuousAt → localMatrixLift_continuousAt
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming localMatrixLift_reconstruct → localMatrixLift_reconstruct
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming localMatrixLift_eventually → localMatrixLift_eventually
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity renaming rightPolynomial → rightPolynomial
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity renaming rightPolynomial_smooth → rightPolynomial_smooth
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity renaming rightPolynomial_det → rightPolynomial_det
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity renaming rightPolynomial_class → rightPolynomial_class
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity renaming archDomain_open → archDomain_open
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming actualSmoothBridge → actualSmoothBridge
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineTarget_one → affineTarget_one
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F]
 abbrev Mat := InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ

 def twoSidedMatrix (p : (Mat F × Mat F) × ArchCoordinates F) : Mat F :=
  fun w => p.1.1 w * rightPolynomial F p.2 w * p.1.2 w

private theorem twoSidedMatrix_smooth : ContDiff ℝ (⊤ : ℕ∞) (twoSidedMatrix F) := by
  apply contDiff_pi.mpr
  intro w
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have hp (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Mat F × Mat F) × ArchCoordinates F => rightPolynomial F p.2 w i j) :=
    ((contDiff_pi.mp (contDiff_pi.mp (contDiff_pi.mp (rightPolynomial_smooth F) w) i) j).comp contDiff_snd)
  simp only [twoSidedMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  fun_prop (disch := exact hp _ _)

private theorem twoSidedMatrix_mem (l r : Mat F) (hl : l ∈ matrixDomain F)
    (hr : r ∈ matrixDomain F) (x : ArchCoordinates F) (hx : x ∈ archDomain F) :
    twoSidedMatrix F ((l,r),x) ∈ matrixDomain F := by
  intro w
  change (l w * rightPolynomial F x w * r w).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul, rightPolynomial_det]
  exact mul_ne_zero (mul_ne_zero (hl w) (hx w)) (hr w)

private theorem twoSidedMatrix_class (l r : Mat F) (hl : l ∈ matrixDomain F)
    (hr : r ∈ matrixDomain F) (x : ArchCoordinates F) (hx : x ∈ archDomain F) :
    matrixClass F (twoSidedMatrix F ((l,r),x)) = matrixClass F l *
      (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))) * matrixClass F r := by
  change matrixClass F (fun w => l w * rightPolynomial F x w * r w) = _
  rw [matrixClass_mul F _ _ (fun w => by rw [Matrix.det_mul, rightPolynomial_det]; exact mul_ne_zero (hl w) (hx w)) hr,
    matrixClass_mul F _ _ hl (fun w => by rw [rightPolynomial_det]; exact hx w), rightPolynomial_class F x hx]

private theorem twoSidedMatrix_jets (f : L F → ℂ) (hf : AffineSmooth F f)
    (l r : Mat F) (hl : l ∈ matrixDomain F) (hr : r ∈ matrixDomain F)
    (x : ArchCoordinates F) (hx : x ∈ archDomain F) (n : ℕ) :
    ContinuousAt (fun p : (Mat F × Mat F) × ArchCoordinates F => iteratedFDeriv ℝ n
      (fun y => f (matrixClass F p.1.1 *
        (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (y w))) * matrixClass F p.1.2)) p.2)
      ((l,r),x) := by
  let W := (matrixDomain F ×ˢ matrixDomain F) ×ˢ archDomain F
  have hW : IsOpen W := ((matrixDomain_open F).prod (matrixDomain_open F)).prod (archDomain_open F)
  have hp : ((l,r),x) ∈ W := ⟨⟨hl,hr⟩,hx⟩
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Mat F × Mat F) × ArchCoordinates F => f (matrixClass F (twoSidedMatrix F p))) W :=
    (matrix_pullback_smooth F f hf).comp (twoSidedMatrix_smooth F).contDiffOn
      (fun p hp => twoSidedMatrix_mem F _ _ hp.1.1 hp.1.2 _ hp.2)
  have hs' : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Mat F × Mat F) × ArchCoordinates F => f (matrixClass F p.1.1 *
        (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (p.2 w))) * matrixClass F p.1.2)) W := by
    apply hs.congr
    intro p hp
    rw [twoSidedMatrix_class F _ _ hp.1.1 hp.1.2 _ hp.2]
  exact ((joint_spatial_jets_on W hW _ hs' n).contDiffAt (hW.mem_nhds hp)).continuousAt

theorem two_sided_parameter_jets {P : Type*} [TopologicalSpace P]
    (f : L F → ℂ) (hf : AffineSmooth F f)
    (l r : P → L F) (hl : Continuous l) (hr : Continuous r) (n : ℕ) :
    ContinuousOn (fun p : ArchCoordinates F × P => iteratedFDeriv ℝ n
      (fun x => f (l p.2 *
        (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))) * r p.2)) p.1)
      (archDomain F ×ˢ univ) := by
  intro p hp
  let ML := localMatrixLift F (l p.2)
  let MR := localMatrixLift F (r p.2)
  have hL := localMatrixLift_reconstruct F (l p.2) (l p.2)
    (show (l p.2)⁻¹ * l p.2 ∈ gaussTarget F by simpa using affineTarget_one F)
  have hR := localMatrixLift_reconstruct F (r p.2) (r p.2)
    (show (r p.2)⁻¹ * r p.2 ∈ gaussTarget F by simpa using affineTarget_one F)
  have hML : ContinuousAt (fun q : ArchCoordinates F × P => ML (l q.2)) p :=
    (localMatrixLift_continuousAt F (l p.2)).comp_of_eq (hl.comp continuous_snd).continuousAt rfl
  have hMR : ContinuousAt (fun q : ArchCoordinates F × P => MR (r q.2)) p :=
    (localMatrixLift_continuousAt F (r p.2)).comp_of_eq (hr.comp continuous_snd).continuousAt rfl
  have hc := (twoSidedMatrix_jets F f hf _ _ hL.1 hR.1 _ hp.1 n).comp_of_eq
    ((hML.prodMk hMR).prodMk continuousAt_fst) rfl
  have heL : ∀ᶠ q : ArchCoordinates F × P in 𝓝 p,
      ML (l q.2) ∈ matrixDomain F ∧ matrixClass F (ML (l q.2)) = l q.2 :=
    (hl.comp continuous_snd).continuousAt (localMatrixLift_eventually F (l p.2))
  have heR : ∀ᶠ q : ArchCoordinates F × P in 𝓝 p,
      MR (r q.2) ∈ matrixDomain F ∧ matrixClass F (MR (r q.2)) = r q.2 :=
    (hr.comp continuous_snd).continuousAt (localMatrixLift_eventually F (r p.2))
  have hEq : (fun q : ArchCoordinates F × P => iteratedFDeriv ℝ n
      (fun x => f (l q.2 * (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))) * r q.2)) q.1)
      =ᶠ[𝓝 p] (fun q => iteratedFDeriv ℝ n (fun x => f (matrixClass F (ML (l q.2)) *
        (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))) * matrixClass F (MR (r q.2)))) q.1) := by
    filter_upwards [heL, heR] with q hqL hqR
    rw [hqL.2, hqR.2]
  exact (hc.congr_of_eventuallyEq hEq).continuousWithinAt

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem two_sided_adelic_spatial_jets
    {P : Type*} [TopologicalSpace P]
    (u : G F ζ hζ → ℂ) (hu : Smooth F ζ hζ u)
    (l r : P → G F ζ hζ) (hl : Continuous l) (hr : Continuous r) (n : ℕ) :
    ContinuousOn
      (fun p : ArchCoordinates F × P => iteratedFDeriv ℝ n
        (fun x => u ((l p.2 * archChart F ζ hζ x) * r p.2)) p.1)
      (archDomain F ×ˢ univ) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  rcases hu.2.2 with ⟨U, hU⟩
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  let S := PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
  have hfinite : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ =
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
    rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure,
      ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
  let bL : P → L F := fun p => (e.symm (l p)).1
  let bR : P → L F := fun p => (e.symm (r p)).1
  let cL : P → KPGlobalTorusFunctionData.finitePart F ζ hζ := fun p =>
    ⟨(e.symm (l p)).2.val, by rw [← hfinite]; exact (e.symm (l p)).2.property⟩
  let cR : P → KPGlobalTorusFunctionData.finitePart F ζ hζ := fun p =>
    ⟨(e.symm (r p)).2.val, by rw [← hfinite]; exact (e.symm (r p)).2.property⟩
  let c : P → KPGlobalTorusFunctionData.finitePart F ζ hζ := fun p => cL p * cR p
  have hbL : Continuous bL := continuous_fst.comp (e.symm.continuous.comp hl)
  have hbR : Continuous bR := continuous_fst.comp (e.symm.continuous.comp hr)
  have hcL : Continuous cL := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_snd.comp (e.symm.continuous.comp hl))
  have hcR : Continuous cR := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_snd.comp (e.symm.continuous.comp hr))
  have hc : Continuous c := hcL.mul hcR
  have hS (d t : L F) : S (d * t) = S d * S t := by
    have hd : e (d, 1) = S d := by simpa using he d 1
    have ht : e (t, 1) = S t := by simpa using he t 1
    rw [← hd, ← ht, ← map_mul]
    simpa using (he (d * t) 1).symm
  have hsplit (p : P) (x : ArchCoordinates F) :
      (l p * archChart F ζ hζ x) * r p =
        S (bL p * (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))) * bR p) * (c p).val := by
    let rx : L F := fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))
    have hchart : e (rx,1) = archChart F ζ hζ x := by
      rw [he, Subgroup.coe_one, mul_one]
      exact (KPLiteralChamber.right_insertion F ζ hζ x).symm
    rw [← e.apply_symm_apply (l p), ← e.apply_symm_apply (r p), ← hchart, ← map_mul, ← map_mul]
    change e ((e.symm (l p)).1 * rx * (e.symm (r p)).1,
      (e.symm (l p)).2 * 1 * (e.symm (r p)).2) = _
    rw [he]
    simp only [mul_one]
    rfl
  intro p hp
  let f : L F → ℂ := fun d => u (S d * (c p.2).val)
  have hfK : KernelSmooth F f := by
    intro d
    have H := KPLiteralChamber.literal_raw_group_chart_contDiffOn_source
      F ζ hζ u hu (S d * (c p.2).val)
    apply H.congr
    intro z hz
    change u (S (ell F z * d) * (c p.2).val) = _
    rw [hS, mul_assoc]
    congr 2
    exact (KPLiteralChamber.left_insertion F ζ hζ z).symm
  have hfA : AffineSmooth F f := (actualSmoothBridge F f).mp hfK
  have hj := two_sided_parameter_jets F f hfA bL bR hbL hbR n
  have hcont := hj p hp
  have hnear : ∀ᶠ q : ArchCoordinates F × P in 𝓝 p,
      (c p.2)⁻¹ * c q.2 ∈ U.toOpenSubgroup := by
    have hN : (U.toOpenSubgroup : Set _) ∈ 𝓝 (1 : KPGlobalTorusFunctionData.finitePart F ζ hζ) :=
      U.toOpenSubgroup.isOpen.mem_nhds U.toOpenSubgroup.one_mem
    exact ((continuous_const.mul (hc.comp continuous_snd)).continuousAt).preimage_mem_nhds
      (by simpa using hN)
  apply hcont.congr_of_eventuallyEq_of_mem ?_ hp
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with q hq
  apply congrArg (fun t => iteratedFDeriv ℝ n t q.1)
  funext x
  have hlevel : ((c p.2)⁻¹ * c q.2).val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    Subgroup.mem_map.mpr ⟨(c p.2)⁻¹ * c q.2, hq, rfl⟩
  rw [hsplit]
  dsimp only [f]
  have He := hU (S (bL q.2 * (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))) * bR q.2) * (c p.2).val)
    ((c p.2)⁻¹ * c q.2).val hlevel
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left] using He

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalComplexSmoothAction.TranslatedGenerators.NativeApproximation

end
