module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCollars.CommutatorWordSupport

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth

open KPGlobalResidualConstruction

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming invertibleProducts_open → invertibleProducts_open
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming matrixPullback_at_units → matrixPullback_at_units
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming productField → productField
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming product_path_hasDeriv → product_path_hasDeriv
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming productRightDerivative_eq_fderiv → productRightDerivative_eq_fderiv
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming productRightDerivative_smooth → productRightDerivative_smooth
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming matrixRightDerivative → matrixRightDerivative
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming rightOmega → rightOmega
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming matrix_omega_right_commutes → matrix_omega_right_commutes
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming matrixRightDerivative_eq_fderiv → matrixRightDerivative_eq_fderiv
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming matrixRightDerivative_smooth → matrixRightDerivative_smooth
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming matrix_omega_smooth → matrix_omega_smooth
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming six_flow_pauli_normalization → six_flow_pauli_normalization
local notation "MP" => MatrixProduct F
local notation "B" => KPSmoothActualFlowData.B F
local notation "O" => invertibleProducts (F := F)
local notation "R" => productRightDerivative (F := F)

 def slotCasimir (v : NumberField.InfinitePlace F) (f : MP → ℂ) : MP → ℂ :=
  fun m => -((1 : ℂ) / 4) *
    (R (v,0) (R (v,0) f) m - R (v,1) (R (v,1) f) m +
    2 * (R (v,2) (R (v,4) f) m + R (v,4) (R (v,2) f) m -
      R (v,3) (R (v,5) f) m - R (v,5) (R (v,3) f) m))

private theorem R_smooth (b : B) (f : MP → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (R b f) O :=
  productRightDerivative_smooth b f invertibleProducts_open hf

private theorem slot_smooth (v : NumberField.InfinitePlace F) (f : MP → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) : ContDiffOn ℝ (⊤ : ℕ∞) (slotCasimir v f) O := by
  unfold slotCasimir
  exact contDiffOn_const.mul (((R_smooth _ _ (R_smooth _ _ hf)).sub
    (R_smooth _ _ (R_smooth _ _ hf))).add (contDiffOn_const.mul
    ((((R_smooth _ _ (R_smooth _ _ hf)).add (R_smooth _ _ (R_smooth _ _ hf))).sub
      (R_smooth _ _ (R_smooth _ _ hf))).sub (R_smooth _ _ (R_smooth _ _ hf)))))

private theorem R_congr (b : B) {f h : MP → ℂ} (he : Set.EqOn f h O)
    {m : MP} (hm : m ∈ O) : R b f m = R b h m := by
  unfold productRightDerivative
  apply Filter.EventuallyEq.deriv_eq
  have hp := (product_path_hasDeriv b m).continuousAt
  have h0 : Function.update m b.1 (m b.1 * NormedSpace.exp
      (((0 : ℝ) : ℂ) • KPSmoothActualFlowData.basisMatrix b.2)) = m := by simp
  have hN : ∀ᶠ n in 𝓝 m, n ∈ O := invertibleProducts_open.mem_nhds hm
  have ht : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), Function.update m b.1 (m b.1 * NormedSpace.exp
      ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b.2)) ∈ O := by
    apply hp.eventually
    simpa only [h0] using hN
  filter_upwards [ht] with t ht
  exact he ht

 theorem slice_smooth (v : NumberField.InfinitePlace F) (m : MP) (hm : m ∈ O)
    (f : MP → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun a => f (Function.update m v a))
      {a : Matrix (Fin 2) (Fin 2) ℂ | a.det ≠ 0} := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (Function.update m v) := by
    apply contDiff_pi.mpr
    intro w
    by_cases hw : w = v <;> simp [hw] <;> fun_prop
  apply hf.comp hs.contDiffOn
  intro a ha w
  by_cases hw : w = v
  · simpa [hw] using ha
  · simpa [hw] using hm w

private theorem slice_R (v : NumberField.InfinitePlace F) (j : Fin 6) (f : MP → ℂ)
    (m : MP) (a : Matrix (Fin 2) (Fin 2) ℂ) :
    R (v,j) f (Function.update m v a) =
      matrixRightDerivative (KPSmoothActualFlowData.basisMatrix j)
        (fun a => f (Function.update m v a)) a := by
  unfold productRightDerivative matrixRightDerivative
  simp

private theorem slice_slot (v : NumberField.InfinitePlace F) (f : MP → ℂ)
    (m : MP) (a : Matrix (Fin 2) (Fin 2) ℂ) :
    slotCasimir v f (Function.update m v a) =
      -((1 : ℂ)/4) *
      (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 0)
        (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 0) (fun a => f (Function.update m v a))) a -
       matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 1)
        (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 1) (fun a => f (Function.update m v a))) a +
       2 * (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 2)
        (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 4) (fun a => f (Function.update m v a))) a +
        matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 4)
        (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 2) (fun a => f (Function.update m v a))) a -
        matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 3)
        (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 5) (fun a => f (Function.update m v a))) a -
        matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 5)
        (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 3) (fun a => f (Function.update m v a))) a)) := by
  unfold slotCasimir
  simp_rw [slice_R]

private theorem R_add (b : B) (f h : MP → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h O)
    (m : MP) (hm : m ∈ O) : R b (fun n => f n + h n) m = R b f m + R b h m := by
  have hd := (hf.differentiableOn (by simp)).differentiableAt (invertibleProducts_open.mem_nhds hm)
  have he := (hh.differentiableOn (by simp)).differentiableAt (invertibleProducts_open.mem_nhds hm)
  change R b (f + h) m = _
  rw [productRightDerivative_eq_fderiv _ _ _ (hd.add he), fderiv_add hd he,
    productRightDerivative_eq_fderiv _ _ _ hd, productRightDerivative_eq_fderiv _ _ _ he]
  rfl

private theorem R_sub (b : B) (f h : MP → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h O)
    (m : MP) (hm : m ∈ O) : R b (fun n => f n - h n) m = R b f m - R b h m := by
  have hd := (hf.differentiableOn (by simp)).differentiableAt (invertibleProducts_open.mem_nhds hm)
  have he := (hh.differentiableOn (by simp)).differentiableAt (invertibleProducts_open.mem_nhds hm)
  change R b (f - h) m = _
  rw [productRightDerivative_eq_fderiv _ _ _ (hd.sub he), fderiv_sub hd he,
    productRightDerivative_eq_fderiv _ _ _ hd, productRightDerivative_eq_fderiv _ _ _ he]
  rfl

private theorem R_mul (b : B) (c : ℂ) (f : MP → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (m : MP) (hm : m ∈ O) :
    R b (fun n => c * f n) m = c * R b f m := by
  have hd := (hf.differentiableOn (by simp)).differentiableAt (invertibleProducts_open.mem_nhds hm)
  rw [productRightDerivative_eq_fderiv _ _ _ (hd.const_mul c), fderiv_const_mul hd c,
    productRightDerivative_eq_fderiv _ _ _ hd]
  rfl

private theorem R_slot_expand (b : B) (v : NumberField.InfinitePlace F) (f : MP → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (m : MP) (hm : m ∈ O) :
    R b (slotCasimir v f) m = -((1 : ℂ) / 4) *
    (R b (R (v,0) (R (v,0) f)) m - R b (R (v,1) (R (v,1) f)) m +
    2 * (R b (R (v,2) (R (v,4) f)) m + R b (R (v,4) (R (v,2) f)) m -
      R b (R (v,3) (R (v,5) f)) m - R b (R (v,5) (R (v,3) f)) m)) := by
  have h2 (i j : Fin 6) := R_smooth (v,i) _ (R_smooth (v,j) _ hf)
  unfold slotCasimir
  rw [R_mul, R_add, R_sub, R_mul, R_sub, R_sub, R_add] <;>
    repeat first | exact hm | exact h2 _ _ | apply ContDiffOn.add |
      apply ContDiffOn.sub | apply ContDiffOn.mul | exact contDiffOn_const

private theorem slot_commute_distinct (b : B) (v : NumberField.InfinitePlace F) (hv : v ≠ b.1)
    (f : MP → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (m : MP) (hm : m ∈ O) :
    slotCasimir v (R b f) m = R b (slotCasimir v f) m := by
  have hc (i j : Fin 6) : R (v,i) (R (v,j) (R b f)) m = R b (R (v,i) (R (v,j) f)) m := by
    have he : Set.EqOn (R (v,j) (R b f)) (R b (R (v,j) f)) O := by
      intro n hn
      exact productRightDerivative_commute_distinct_places _ _ hv _ invertibleProducts_open hf n hn
    rw [R_congr _ he hm]
    exact productRightDerivative_commute_distinct_places _ _ hv _ invertibleProducts_open (R_smooth _ _ hf) m hm
  rw [R_slot_expand b v f hf m hm]
  unfold slotCasimir
  simp_rw [hc]

 theorem slice_slot_omega (v : NumberField.InfinitePlace F) (f : MP → ℂ)
    (m : MP) (hm : m ∈ O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (a : Matrix (Fin 2) (Fin 2) ℂ) (ha : a.det ≠ 0) :
    slotCasimir v f (Function.update m v a) =
      -((1 : ℂ)/2) * rightOmega (fun a => f (Function.update m v a)) a := by
  rw [slice_slot]
  exact six_flow_pauli_normalization _ (isOpen_ne.preimage (by fun_prop))
    (slice_smooth v m hm f hf) a ha

private theorem slot_commute_same (v : NumberField.InfinitePlace F) (j : Fin 6)
    (f : MP → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (m : MP) (hm : m ∈ O) :
    slotCasimir v (R (v,j) f) m = R (v,j) (slotCasimir v f) m := by
  let phi := fun a => f (Function.update m v a)
  let D : Set (Matrix (Fin 2) (Fin 2) ℂ) := {a | a.det ≠ 0}
  have hD : IsOpen D := isOpen_ne.preimage (by fun_prop)
  have hp : ContDiffOn ℝ (⊤ : ℕ∞) phi D := slice_smooth v m hm f hf
  have hs : (fun a => R (v,j) f (Function.update m v a)) = matrixRightDerivative (KPSmoothActualFlowData.basisMatrix j) phi := by
    funext a; exact slice_R v j f m a
  have hm0 : Function.update m v (m v) = m := Function.update_eq_self v m
  have hc := matrix_omega_right_commutes (KPSmoothActualFlowData.basisMatrix j) phi hD hp
    (Matrix.GeneralLinearGroup.mkOfDetNeZero (m v) (hm v)) (hm v)
  change rightOmega (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix j) phi) (m v) =
    matrixRightDerivative (KPSmoothActualFlowData.basisMatrix j) (rightOmega phi) (m v) at hc
  rw [← hm0, slice_slot_omega v _ m hm (R_smooth _ _ hf) _ (hm v), hs, hc, slice_R]
  have he : (fun a => slotCasimir v f (Function.update m v a)) =ᶠ[𝓝 (m v)]
      (fun a => -((1 : ℂ)/2) * rightOmega phi a) := by
    filter_upwards [hD.mem_nhds (hm v)] with a ha
    exact slice_slot_omega v f m hm hf a ha
  have hd1 := (slice_smooth v m hm _ (slot_smooth v f hf)).differentiableOn (by simp)
    |>.differentiableAt (hD.mem_nhds (hm v))
  have hd2 := (matrix_omega_smooth phi hD hp).differentiableOn (by simp)
    |>.differentiableAt (hD.mem_nhds (hm v))
  rw [matrixRightDerivative_eq_fderiv _ _ _ hd1, he.fderiv_eq,
    fderiv_const_mul hd2, matrixRightDerivative_eq_fderiv _ _ _ hd2]
  rfl

 def productCasimir (f : MP → ℂ) : MP → ℂ := fun m => ∑ v, slotCasimir v f m

private theorem R_sum {ι : Type} (u : Finset ι) (b : B) (f : ι → MP → ℂ)
    (hf : ∀ i ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (f i) O) (m : MP) (hm : m ∈ O) :
    R b (fun n => ∑ i ∈ u, f i n) m = ∑ i ∈ u, R b (f i) m := by
  have hd (i) (hi : i ∈ u) := (hf i hi).differentiableOn (by simp)
    |>.differentiableAt (invertibleProducts_open.mem_nhds hm)
  have hdS := DifferentiableAt.fun_sum hd
  rw [productRightDerivative_eq_fderiv _ _ _ hdS]
  have heq : (fun y => ∑ i ∈ u, f i y) = ∑ i ∈ u, f i := by
    funext y
    simp only [Finset.sum_apply]
  rw [heq, fderiv_sum hd]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [productRightDerivative_eq_fderiv _ _ _ (hd i hi)]

private theorem product_commute (b : B) (f : MP → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (m : MP) (hm : m ∈ O) :
    productCasimir (R b f) m = R b (productCasimir f) m := by
  unfold productCasimir
  rw [R_sum _ _ _ (fun v _ => slot_smooth v f hf) m hm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = b.1
  · subst v; exact slot_commute_same _ _ f hf m hm
  · exact slot_commute_distinct b v hv f hf m hm

private theorem productWord_smooth (w : List B) (f : MP → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (productRightWord w f) O := by
  induction w with
  | nil => exact hf
  | cons b w ih => exact R_smooth b _ ih

 theorem productWord_congr (w : List B) {f h : MP → ℂ} (he : Set.EqOn f h O) :
    Set.EqOn (productRightWord w f) (productRightWord w h) O := by
  induction w with
  | nil => exact he
  | cons b w ih => intro m hm; exact R_congr b ih hm

private theorem product_word_commute (w : List B) (f : MP → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) :
    Set.EqOn (productCasimir (productRightWord w f)) (productRightWord w (productCasimir f)) O := by
  induction w with
  | nil => intro m hm; rfl
  | cons b w ih =>
    intro m hm
    change productCasimir (R b (productRightWord w f)) m = R b (productRightWord w (productCasimir f)) m
    rw [product_commute _ _ (productWord_smooth w f hf) m hm, R_congr b ih hm]

 theorem matrixPullback_casimir_units (f : G → ℂ) (g : G)
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    matrixPullback (KPMsGreenFlux.casimir F ζ hζ f) g (fun v => (a v).val) =
      productCasimir (matrixPullback f g) (fun v => (a v).val) := by
  have h2 (v : NumberField.InfinitePlace F) (i j : Fin 6) :=
    matrixPullback_rightWord [(v,i),(v,j)] f g a
  simp only [List.foldr_cons, List.foldr_nil, productRightWord] at h2
  rw [matrixPullback_at_units]
  unfold KPMsGreenFlux.casimir productCasimir slotCasimir
  apply Finset.sum_congr rfl
  intro v _
  have he (i j : Fin 6) := h2 v i j
  simp only [matrixPullback_at_units] at he
  simp_rw [he]

private theorem matrixPullback_casimir_eqOn (f : G → ℂ) (g : G) :
    Set.EqOn (matrixPullback (KPMsGreenFlux.casimir F ζ hζ f) g)
      (productCasimir (matrixPullback f g)) O := by
  intro m hm
  exact matrixPullback_casimir_units f g (fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero (m v) (hm v))

private theorem native_fold_commute (f : G → ℂ)
    (hf : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (a * archChart F ζ hζ x)) (archDomain F))
    (w : List B) (g : G) :
    KPMsGreenFlux.casimir F ζ hζ (w.foldr (fun b h => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 h) f) g =
    w.foldr (fun b h => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 h)
      (KPMsGreenFlux.casimir F ζ hζ f) g := by
  let a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun _ => 1
  have ha : (fun v => (a v).val) ∈ O := fun v => Matrix.GeneralLinearGroup.det_ne_zero (a v)
  have hp (h : G → ℂ) : matrixPullback h g (fun v => (a v).val) = h g := by
    rw [matrixPullback_at_units]
    have he : (fun v => Matrix.ProjGenLinGroup.mk (a v)) = 1 := by ext v; simp [a]
    rw [he, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, mul_one]
  rw [← hp (KPMsGreenFlux.casimir F ζ hζ
    (w.foldr (fun b h => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 h) f)), matrixPullback_casimir_units]
  have he : Set.EqOn
      (matrixPullback (w.foldr (fun b h => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 h) f) g)
      (productRightWord w (matrixPullback f g)) O := by
    intro m hm
    exact matrixPullback_rightWord w f g (fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero (m v) (hm v))
  have he2 : Set.EqOn (productCasimir
      (matrixPullback (w.foldr (fun b h => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 h) f) g))
      (productCasimir (productRightWord w (matrixPullback f g))) O := by
    intro m hm
    unfold productCasimir slotCasimir
    apply Finset.sum_congr rfl
    intro v _
    have h2 (i j : Fin 6) := productWord_congr [(v,i),(v,j)] he hm
    simp only [productRightWord] at h2
    simp_rw [h2]
  rw [he2 ha, product_word_commute w _ (matrixPullback_smooth f hf g) ha]
  rw [← productWord_congr w (matrixPullback_casimir_eqOn f g) ha,
    ← matrixPullback_rightWord, hp]

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart renaming word_reindex → word_reindex

theorem native_casimir_commutes_word
    (f : G → ℂ)
    (hf : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => f (a * archChart F ζ hζ x)) (archDomain F))
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (g : G) :
    KPMsGreenFlux.casimir F ζ hζ
      (KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w f) g =
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
      (KPMsGreenFlux.casimir F ζ hζ f) g := by
  simp_rw [word_reindex]
  exact native_fold_commute f hf _ g

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth

end
