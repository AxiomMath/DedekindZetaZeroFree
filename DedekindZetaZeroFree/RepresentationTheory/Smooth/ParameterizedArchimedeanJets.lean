module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactAverages.TaylorJets
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.BigCellSectionSmoothness
public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity
open KPLiteralRaw

open Set Filter Topology
open scoped Matrix.Norms.Elementwise
open KPSpatialSmoothing.ArchKernel hiding G
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
set_option maxHeartbeats 400000
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming actualSmoothBridge → actualSmoothBridge
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineTarget_one → affineTarget_one

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 abbrev Mat := InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ

def rightPolynomial (x : KPGlobalResidualConstruction.ArchCoordinates F) : Mat F :=
  fun w => !![x w 1 + x w 0 * x w 2, x w 0; x w 2, 1]

theorem rightPolynomial_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (rightPolynomial F) := by
  apply contDiff_pi.mpr
  intro w
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : KPGlobalResidualConstruction.ArchCoordinates F => x w 1 + x w 0 * x w 2)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : KPGlobalResidualConstruction.ArchCoordinates F => x w 0)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : KPGlobalResidualConstruction.ArchCoordinates F => x w 2)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun _ => (1 : ℂ))
    fun_prop

omit [NumberField F] in
theorem rightPolynomial_det (x : KPGlobalResidualConstruction.ArchCoordinates F)
    (w : InfinitePlace F) : (rightPolynomial F x w).det = x w 1 := by
  simp [rightPolynomial, Matrix.det_fin_two]

theorem archDomain_open : IsOpen (KPGlobalResidualConstruction.archDomain F) := by
  have he : KPGlobalResidualConstruction.archDomain F =
      ⋂ w, {x : KPGlobalResidualConstruction.ArchCoordinates F | x w 1 ≠ 0} := by
    ext x
    simp [KPGlobalResidualConstruction.archDomain]
  rw [he]
  apply isOpen_iInter_of_finite
  intro w
  exact isOpen_ne_fun ((continuous_apply 1).comp (continuous_apply w)) continuous_const

omit [NumberField F] in
theorem rightPolynomial_class (x : KPGlobalResidualConstruction.ArchCoordinates F)
    (hx : x ∈ KPGlobalResidualConstruction.archDomain F) :
    matrixClass F (rightPolynomial F x) =
      fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w)) := by
  funext w
  have hd : (rightPolynomial F x w).det ≠ 0 := by
    rw [rightPolynomial_det]
    exact hx w
  simp only [matrixClass, dite_eq_left hd]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change rightPolynomial F x w i j = _
  rw [KPLiteralChamber.rightMatrix_val _ (hx w)]
  rfl

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity

end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity
open KPLiteralRaw

open Set Filter Topology
open scoped Matrix.Norms.Elementwise
open KPSpatialSmoothing.ArchKernel hiding G
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
set_option maxHeartbeats 400000
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming actualSmoothBridge → actualSmoothBridge
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineTarget_one → affineTarget_one

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

set_option backward.isDefEq.respectTransparency false in
private theorem right_parameter_jets {P : Type*} [TopologicalSpace P]
    (f : L F → ℂ) (hf : AffineSmooth F f) (b : P → L F) (hb : Continuous b) (n : ℕ) :
    ContinuousOn (fun p : KPGlobalResidualConstruction.ArchCoordinates F × P =>
      iteratedFDeriv ℝ n (fun x => f
        ((fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))) * b p.2)) p.1)
      (KPGlobalResidualConstruction.archDomain F ×ˢ univ) := by
  let T : Mat F × KPGlobalResidualConstruction.ArchCoordinates F → Mat F :=
    fun p w => rightPolynomial F p.2 w * p.1 w
  have hT : ContDiff ℝ (⊤ : ℕ∞) T := by
    apply contDiff_pi.mpr
    intro w
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    have hc (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : Mat F × KPGlobalResidualConstruction.ArchCoordinates F =>
          rightPolynomial F p.2 w i j) :=
      ((contDiff_pi.mp (contDiff_pi.mp (contDiff_pi.mp
        (rightPolynomial_smooth F) w) i) j).comp contDiff_snd)
    simp only [T, Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop (disch := exact hc _ _)
  let W := matrixDomain F ×ˢ KPGlobalResidualConstruction.archDomain F
  have hW : IsOpen W := (matrixDomain_open F).prod (archDomain_open F)
  have hTW : MapsTo T W (matrixDomain F) := by
    intro p hp w
    change (rightPolynomial F p.2 w * p.1 w).det ≠ 0
    rw [Matrix.det_mul, rightPolynomial_det]
    exact mul_ne_zero (hp.2 w) (hp.1 w)
  have hs := (matrix_pullback_smooth F f hf).comp hT.contDiffOn hTW
  have hj := joint_spatial_jets_on W hW (fun p => f (matrixClass F (T p))) hs n
  intro p hp
  let M := localMatrixLift F (b p.2)
  have hM := localMatrixLift_reconstruct F (b p.2) (b p.2)
    (show (b p.2)⁻¹ * b p.2 ∈ gaussTarget F by simpa using affineTarget_one F)
  have hMc : ContinuousAt (fun q : KPGlobalResidualConstruction.ArchCoordinates F × P =>
      M (b q.2)) p :=
    (localMatrixLift_continuousAt F (b p.2)).comp_of_eq
      (hb.comp continuous_snd).continuousAt rfl
  have hjet : ContinuousAt (fun q : Mat F × KPGlobalResidualConstruction.ArchCoordinates F =>
      iteratedFDeriv ℝ n (fun x => f (matrixClass F (T (q.1, x)))) q.2)
      (M (b p.2), p.1) :=
    ((hj (M (b p.2), p.1) ⟨hM.1, hp.1⟩).contDiffAt
      (hW.mem_nhds (show (M (b p.2), p.1) ∈ W from ⟨hM.1, hp.1⟩))).continuousAt
  have hc := hjet.comp_of_eq (hMc.prodMk continuousAt_fst) rfl
  have heM : ∀ᶠ q : KPGlobalResidualConstruction.ArchCoordinates F × P in 𝓝 p,
      M (b q.2) ∈ matrixDomain F ∧ matrixClass F (M (b q.2)) = b q.2 :=
    (hb.comp continuous_snd).continuousAt (localMatrixLift_eventually F (b p.2))
  have heD : ∀ᶠ q : KPGlobalResidualConstruction.ArchCoordinates F × P in 𝓝 p,
      q.1 ∈ KPGlobalResidualConstruction.archDomain F :=
    continuousAt_fst.preimage_mem_nhds ((archDomain_open F).mem_nhds hp.1)
  apply (hc.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [heM, heD] with q hqM hqD
  apply Filter.EventuallyEq.eq_of_nhds
  apply Filter.EventuallyEq.iteratedFDeriv
  filter_upwards [(archDomain_open F).mem_nhds hqD] with x hx
  change f ((fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))) * b q.2) =
    f (matrixClass F (T (M (b q.2), x)))
  rw [show T (M (b q.2), x) = fun w => rightPolynomial F x w * M (b q.2) w from rfl,
    matrixClass_mul F _ _ (fun w => by rw [rightPolynomial_det]; exact hx w) hqM.1,
    rightPolynomial_class F x hx, hqM.2]

theorem continuous_parameter_arch_spatial_jets
    {P : Type*} [TopologicalSpace P]
    (u : Functions F ζ hζ) (hu : Smooth F ζ hζ u)
    (g : G F ζ hζ) (a : P → G F ζ hζ) (ha : Continuous a) (n : ℕ) :
    ContinuousOn
      (fun p : KPGlobalResidualConstruction.ArchCoordinates F × P =>
        iteratedFDeriv ℝ n
          (fun x => u ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * a p.2))
          p.1)
      (KPGlobalResidualConstruction.archDomain F ×ˢ Set.univ) := by
  rcases hu.2.2 with ⟨U, hU⟩
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  let S := PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
  have hfinite : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ =
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
    rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure,
      ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
  let b : P → L F := fun p => (e.symm (a p)).1
  let c : P → KPGlobalTorusFunctionData.finitePart F ζ hζ := fun p =>
    ⟨(e.symm (a p)).2.val, by rw [← hfinite]; exact (e.symm (a p)).2.property⟩
  have hb : Continuous b := continuous_fst.comp (e.symm.continuous.comp ha)
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_snd.comp (e.symm.continuous.comp ha))
  have haeq (p : P) : a p = S (b p) * (c p).val :=
    (e.apply_symm_apply (a p)).symm.trans (he _ _)
  have hS (d t : L F) : S (d * t) = S d * S t := by
    have hd : e (d, 1) = S d := by simpa using he d 1
    have ht : e (t, 1) = S t := by simpa using he t 1
    rw [← hd, ← ht, ← map_mul]
    simpa using (he (d * t) 1).symm
  let v : Functions F ζ hζ := fun t => u (g * t)
  have hv : Smooth F ζ hζ v := by
    refine ⟨hu.1.comp (continuous_const.mul continuous_id), ?_, U, ?_⟩
    · intro t
      simpa only [v, mul_assoc] using hu.2.1 (g * t)
    · intro t k hk
      simpa only [v, mul_assoc] using hU (g * t) k hk
  intro p hp
  let f : L F → ℂ := fun d => v (S d * (c p.2).val)
  have hfK : KernelSmooth F f := by
    intro d
    have H := KPLiteralChamber.literal_raw_group_chart_contDiffOn_source
      F ζ hζ v hv (S d * (c p.2).val)
    apply H.congr
    intro z hz
    change v (S (ell F z * d) * (c p.2).val) = _
    rw [hS, mul_assoc]
    congr 2
    exact (KPLiteralChamber.left_insertion F ζ hζ z).symm
  have hfA : AffineSmooth F f := (actualSmoothBridge F f).mp hfK
  have hj := right_parameter_jets F f hfA b hb n
  have hcont := hj p hp
  have hnear : ∀ᶠ q : KPGlobalResidualConstruction.ArchCoordinates F × P in 𝓝 p,
      (c p.2)⁻¹ * c q.2 ∈ U.toOpenSubgroup := by
    have hN : (U.toOpenSubgroup : Set _) ∈ 𝓝 (1 : KPGlobalTorusFunctionData.finitePart F ζ hζ) :=
      U.toOpenSubgroup.isOpen.mem_nhds U.toOpenSubgroup.one_mem
    exact ((continuous_const.mul (hc.comp continuous_snd)).continuousAt).preimage_mem_nhds
      (by simpa using hN)
  apply hcont.congr_of_eventuallyEq_of_mem ?_ hp
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with q hq
  apply congrArg (fun t => iteratedFDeriv ℝ n t q.1)
  funext x
  let r : L F := fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x w))
  have hxS : KPGlobalResidualConstruction.archChart F ζ hζ x = S r :=
    KPLiteralChamber.right_insertion F ζ hζ x
  have hlevel : ((c p.2)⁻¹ * c q.2).val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    Subgroup.mem_map.mpr ⟨(c p.2)⁻¹ * c q.2, hq, rfl⟩
  change u ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * a q.2) =
    u (g * (S (r * b q.2) * (c p.2).val))
  rw [hxS, haeq]
  have He := hU (g * (S (r * b q.2) * (c p.2).val))
    ((c p.2)⁻¹ * c q.2).val hlevel
  simpa only [hS, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc,
    mul_inv_cancel_left] using He

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity

end
end
