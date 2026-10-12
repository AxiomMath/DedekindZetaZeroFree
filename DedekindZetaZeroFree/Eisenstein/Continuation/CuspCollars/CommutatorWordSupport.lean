module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ActualNativeWordIdentification
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.ChamberCasimir

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth
open KPGlobalResidualConstruction KPLiteralChamber
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming rightCoordinates_nonzero → rightCoordinates_nonzero
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ
abbrev MatrixProduct (F : Type) [Field F] [NumberField F] :=
  NumberField.InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ

def invertibleProducts : Set (MatrixProduct F) := {m | ∀ w, (m w).det ≠ 0}

def matrixPullback (f : G → ℂ) (g : G) (m : MatrixProduct F) : ℂ :=
  if hm : m ∈ invertibleProducts then f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (fun w => Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero (m w) (hm w))))
  else 0

 theorem invertibleProducts_open : IsOpen (invertibleProducts (F := F)) := by
  have he : invertibleProducts (F := F) = ⋂ w, {m : MatrixProduct F | (m w).det ≠ 0} := by
    ext m; simp [invertibleProducts]
  rw [he]
  exact isOpen_iInter_of_finite (fun w => isOpen_ne.preimage (by fun_prop))

theorem matrixPullback_smooth (f : G → ℂ)
    (hf : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => f (a * archChart F ζ hζ x)) (archDomain F)) (g : G) :
    ContDiffOn ℝ (⊤ : ℕ∞) (matrixPullback f g) (invertibleProducts (F := F)) := by
  apply contDiffOn_of_locally_contDiffOn
  intro a ha
  let A := fun w => Matrix.GeneralLinearGroup.mkOfDetNeZero (a w) (ha w)
  let M := fun (m : MatrixProduct F) w => ((A w)⁻¹).val * m w
  let O := invertibleProducts (F := F) ∩ {m | ∀ w, M m w 1 1 ≠ 0}
  let q := fun (m : MatrixProduct F) w => rightCoordinates (M m w)
  have hM (w) : ContDiff ℝ (⊤ : ℕ∞) (fun m : MatrixProduct F => M m w) := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    simp only [M, Matrix.mul_apply]
    apply ContDiff.sum; intro k _
    exact contDiff_const.mul
      ((ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).contDiff.comp
        ((ContinuousLinearMap.proj k : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).contDiff.comp
          (ContinuousLinearMap.proj w : MatrixProduct F →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ).contDiff))
  have hentry (w) (i j : Fin 2) :
      ContDiff ℝ (⊤ : ℕ∞) (fun m : MatrixProduct F => M m w i j) := by
    exact (contDiff_pi.mp (contDiff_pi.mp (hM w) i)) j
  have hO : IsOpen O := by
    apply invertibleProducts_open.inter
    have he : {m : MatrixProduct F | ∀ w, M m w 1 1 ≠ 0} =
        ⋂ w, {m : MatrixProduct F | M m w 1 1 ≠ 0} := by ext m; simp
    rw [he]
    exact isOpen_iInter_of_finite (fun w => isOpen_ne.preimage (hentry w 1 1).continuous)
  have hMa (w) : M a w = 1 := by
    change ((A w)⁻¹).val * (A w).val = 1
    exact congrArg Units.val (inv_mul_cancel (A w))
  have haO : a ∈ O := by
    exact ⟨ha, fun w => by rw [hMa]; simp⟩
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q O := by
    apply contDiffOn_pi.mpr; intro w
    apply contDiffOn_pi.mpr; intro i
    have hn : ∀ m ∈ O, M m w 1 1 ≠ 0 := fun _ hm => hm.2 w
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun m : MatrixProduct F => (M m w).det) := by
      simp only [Matrix.det_fin_two]
      exact ((hentry w 0 0).mul (hentry w 1 1)).sub ((hentry w 0 1).mul (hentry w 1 0))
    fin_cases i <;> simp [q, rightCoordinates]
    · simpa only [div_eq_mul_inv] using! (hentry w 0 1).contDiffOn.mul ((hentry w 1 1).contDiffOn.inv hn)
    · simpa only [div_eq_mul_inv] using! hd.contDiffOn.mul
        (((hentry w 1 1).pow 2).contDiffOn.inv (fun m hm => pow_ne_zero _ (hn m hm)))
    · simpa only [div_eq_mul_inv] using! (hentry w 1 0).contDiffOn.mul ((hentry w 1 1).contDiffOn.inv hn)
  have hqD : Set.MapsTo q O (archDomain F) := by
    intro m hm w
    let B := Matrix.GeneralLinearGroup.mkOfDetNeZero (m w) (hm.1 w)
    exact rightCoordinates_nonzero ((A w)⁻¹ * B) (hm.2 w)
  let b : G := g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (fun w => Matrix.ProjGenLinGroup.mk (A w))
  have hs := (hf b).comp hq hqD
  refine ⟨O, hO, haO, (hs.mono Set.inter_subset_right).congr ?_⟩
  intro m hm
  change m ∈ invertibleProducts ∧ m ∈ O at hm
  change matrixPullback f g m = f (b * archChart F ζ hζ (q m))
  dsimp only [b]
  rw [matrixPullback, dite_eq_left hm.1, right_insertion]
  rw [mul_assoc, ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  congr 3
  funext w
  let B := Matrix.GeneralLinearGroup.mkOfDetNeZero (m w) (hm.1 w)
  change Matrix.ProjGenLinGroup.mk B =
    Matrix.ProjGenLinGroup.mk (A w) * Matrix.ProjGenLinGroup.mk (rightMatrix (q m w))
  rw [show q m w = rightCoordinates (((A w)⁻¹ * B).val) from rfl,
    rightCoordinates_reconstruct ((A w)⁻¹ * B) (hm.2.2 w), ← map_mul]
  simp

open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming native_flow_single → native_flow_single

def productRightDerivative (b : KPSmoothActualFlowData.B F)
    (f : MatrixProduct F → ℂ) (m : MatrixProduct F) : ℂ :=
  deriv (fun t : ℝ => f (Function.update m b.1
    (m b.1 * NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b.2)))) 0

 theorem matrixPullback_at_units (f : G → ℂ) (g : G)
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    matrixPullback f g (fun w => (a w).val) =
      f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w))) := by
  have ha : (fun w => (a w).val) ∈ invertibleProducts (F := F) :=
    fun w => Matrix.GeneralLinearGroup.det_ne_zero (a w)
  rw [matrixPullback, dite_eq_left ha]
  congr 3
  funext w
  congr 1
  exact Units.ext rfl

theorem matrixPullback_rightDerivative (b : KPSmoothActualFlowData.B F)
    (f : G → ℂ) (g : G)
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    matrixPullback (KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 f) g
      (fun w => (a w).val) =
    productRightDerivative b (matrixPullback f g) (fun w => (a w).val) := by
  rw [matrixPullback_at_units]
  unfold KPMsGreenFlux.rightDerivative productRightDerivative
  apply congrArg (fun q : ℝ → ℂ => deriv q 0)
  funext t
  let e := KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b.2)
  have hmat : Function.update (fun w => (a w).val) b.1
      ((a b.1).val * NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b.2)) =
      fun w => ((Function.update a b.1 (a b.1 * e)) w).val := by
    funext w
    by_cases hw : w = b.1 <;> simp [hw, e, KPSmoothActualFlowData.matrixExponential]
  rw [hmat, matrixPullback_at_units, native_flow_single F]
  rw [mul_assoc, ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  congr 3
  funext w
  by_cases hw : w = b.1
  · subst w
    simp only [Pi.mul_apply, Function.update_self, map_mul]
    rfl
  · simp only [Pi.mul_apply, Function.update_of_ne hw, mul_one]

def productRightWord : List (KPSmoothActualFlowData.B F) →
    (MatrixProduct F → ℂ) → MatrixProduct F → ℂ
  | [], f => f
  | b :: w, f => productRightDerivative b (productRightWord w f)

theorem matrixPullback_rightWord (w : List (KPSmoothActualFlowData.B F))
    (f : G → ℂ) (g : G)
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    matrixPullback (w.foldr (fun b h =>
      KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 h) f) g
      (fun v => (a v).val) =
    productRightWord w (matrixPullback f g) (fun v => (a v).val) := by
  induction w generalizing a with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldr_cons, matrixPullback_rightDerivative]
    unfold productRightWord productRightDerivative
    apply congrArg (fun q : ℝ → ℂ => deriv q 0)
    funext t
    let e := KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b.2)
    have hmat : Function.update (fun v => (a v).val) b.1
        ((a b.1).val * NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b.2)) =
        fun v => ((Function.update a b.1 (a b.1 * e)) v).val := by
      funext v
      by_cases hv : v = b.1 <;> simp [hv, e, KPSmoothActualFlowData.matrixExponential]
    rw [hmat]
    exact ih _

open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming exp_path_hasDeriv → exp_path_hasDeriv

 def productField (b : KPSmoothActualFlowData.B F) : MatrixProduct F →L[ℝ] MatrixProduct F :=
  LinearMap.toContinuousLinearMap
    { toFun := fun m => Pi.single b.1 (m b.1 * KPSmoothActualFlowData.basisMatrix b.2)
      map_add' := by
        intro m n; ext v i j
        by_cases hv : v = b.1 <;> simp [hv, Matrix.add_mul]
      map_smul' := by
        intro r m; ext v i j
        by_cases hv : v = b.1 <;> simp [hv] }

 theorem product_path_hasDeriv (b : KPSmoothActualFlowData.B F) (m : MatrixProduct F) :
    HasDerivAt (fun t : ℝ => Function.update m b.1
      (m b.1 * NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b.2)))
      (productField b m) 0 := by
  apply hasDerivAt_pi.mpr
  intro v
  by_cases hv : v = b.1
  · subst v
    simpa [productField] using exp_path_hasDeriv (m b.1) (KPSmoothActualFlowData.basisMatrix b.2)
  · simpa [hv, productField] using (hasDerivAt_const (0 : ℝ) (m v))

 theorem productRightDerivative_eq_fderiv (b : KPSmoothActualFlowData.B F)
    (f : MatrixProduct F → ℂ) (m : MatrixProduct F) (hf : DifferentiableAt ℝ f m) :
    productRightDerivative b f m = fderiv ℝ f m (productField b m) := by
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 (product_path_hasDeriv b m)
    (by simp)).deriv

 theorem productRightDerivative_smooth (b : KPSmoothActualFlowData.B F)
    (f : MatrixProduct F → ℂ) {O : Set (MatrixProduct F)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (productRightDerivative b f) O := by
  apply ((hf.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (productField b).contDiff.contDiffOn).congr
  intro m hm
  exact productRightDerivative_eq_fderiv b f m
    ((hf.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hm))

private theorem productRightDerivative_twice (b c : KPSmoothActualFlowData.B F)
    (f : MatrixProduct F → ℂ) {O : Set (MatrixProduct F)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (m : MatrixProduct F) (hm : m ∈ O) :
    productRightDerivative b (productRightDerivative c f) m =
      fderiv ℝ (fderiv ℝ f) m (productField b m) (productField c m) +
        fderiv ℝ f m (productField c (productField b m)) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) m :=
    ((hf.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).differentiableOn
      (by simp)).differentiableAt (hO.mem_nhds hm)
  have he : productRightDerivative c f =ᶠ[𝓝 m]
      (fun n => fderiv ℝ f n (productField c n)) := by
    filter_upwards [hO.mem_nhds hm] with n hn
    exact productRightDerivative_eq_fderiv c f n
      ((hf.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hn))
  have hh := hd.hasFDerivAt.clm_apply (productField c).hasFDerivAt
  rw [productRightDerivative_eq_fderiv b _ m
    (hh.differentiableAt.congr_of_eventuallyEq he), he.fderiv_eq]
  have heq := congrArg (fun D : MatrixProduct F →L[ℝ] ℂ => D (productField b m)) hh.fderiv
  exact heq.trans (by simp only [add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]; ring)

theorem productRightDerivative_commute_distinct_places
    (b c : KPSmoothActualFlowData.B F) (hbc : b.1 ≠ c.1)
    (f : MatrixProduct F → ℂ) {O : Set (MatrixProduct F)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (m : MatrixProduct F) (hm : m ∈ O) :
    productRightDerivative b (productRightDerivative c f) m =
      productRightDerivative c (productRightDerivative b f) m := by
  rw [productRightDerivative_twice b c f hO hf m hm,
    productRightDerivative_twice c b f hO hf m hm]
  have hz : productField c (productField b m) = 0 ∧
      productField b (productField c m) = 0 := by
    constructor <;> ext v i j <;> simp [productField, hbc, hbc.symm]
  simp only [hz.1, hz.2, map_zero, add_zero]
  exact ((hf.contDiffAt (hO.mem_nhds hm)).isSymmSndFDerivAt (by simp)).eq _ _

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth

end
