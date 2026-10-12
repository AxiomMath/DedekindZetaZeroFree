module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ArchimedeanCasimir
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.UniformL2Tails

@[expose] public section

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric
open KPSmoothActualFlowData
open KPMsGreenFlux.FramedConormal.NativeShellStokes.IwasawaFieldJets
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric renaming localD_first → localD_first
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric renaming localD_left → localD_left
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric renaming first_precomp → first_precomp

def localEnergy (f : Matrix.GeneralLinearGroup (Fin 2) ℂ → ℂ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) : ℝ :=
  (‖localD 0 f g‖^2 + ‖localD 1 f g‖^2) / 4 +
    (‖localD 2 f g‖^2 + ‖localD 3 f g‖^2 + ‖localD 4 f g‖^2 + ‖localD 5 f g‖^2) / 2

theorem basepoint_energy (φ : KPArch.H3 → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    localEnergy (fun a => φ (KPArch.action a (0,0))) 1 =
      ‖fderiv ℝ φ (0,0) (0,1)‖^2 + ‖fderiv ℝ φ (0,0) (1,0)‖^2 +
        ‖fderiv ℝ φ (0,0) (Complex.I,0)‖^2 := by
  have h2 : ((0,2) : KPArch.H3) = (2 : ℝ) • (0,1) := by ext <;> norm_num
  have hzero : ((0,0) : KPArch.H3) = 0 := rfl
  have hi : ((-Complex.I,0) : KPArch.H3) = -(Complex.I,0) := by ext <;> simp
  simp only [localEnergy, localD_first φ hφ, (KPArch.action_laws 1 1 (0,0)).1, Units.val_one]
  norm_num [horizontalFieldJet, verticalFieldJet, horizontalNumeratorJet,
    horizontalNumerator, bottomDenominatorJet, bottomDenominator, basisMatrix, sl2Matrix,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [h2, hzero, hi, map_smul, map_neg, map_zero, norm_smul, norm_neg, norm_zero]
  norm_num
  ring

private theorem localEnergy_left (f : Matrix.GeneralLinearGroup (Fin 2) ℂ → ℂ)
    (a g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    localEnergy (fun x => f (a*x)) g = localEnergy f (a*g) := by
  simp only [localEnergy, localD_left]

def productEnergy (d : ℕ) (f : KPArch.Space d → ℂ)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) : ℝ :=
  ∑ i : Fin d, localEnergy
    (fun a => f (fun k => KPArch.action (Function.update g i a k) (0,0))) (g i)

theorem product_basepoint_energy (d : ℕ) (f : KPArch.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    productEnergy d f (fun _ => 1) =
      ∑ i : Fin d, ∑ j : Fin 3,
        ‖fderiv ℝ f 0 (KPContFlatCuspCasimirSpecialization.coordinateDirection d i j)‖^2 := by
  unfold productEnergy
  apply Finset.sum_congr rfl
  intro i _
  let L : KPArch.H3 →L[ℝ] KPArch.Space d := ContinuousLinearMap.single ℝ (fun _ : Fin d => KPArch.H3) i
  have he (a : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
      (fun k => KPArch.action (Function.update (fun _ : Fin d => (1 : Matrix.GeneralLinearGroup (Fin 2) ℂ)) i a k) (0,0)) =
        L (KPArch.action a (0,0)) := by
    funext k
    by_cases hk : k = i
    · subst k; simp [L]
    · simp [L, Function.update_of_ne hk, Pi.single_eq_of_ne hk, (KPArch.action_laws 1 1 (0,0)).1]
  simp_rw [he]
  have hb := basepoint_energy (f ∘ L) (hf.comp L.contDiff)
  change localEnergy (fun a => f (L (KPArch.action a (0,0)))) 1 = _ at hb
  rw [hb, first_precomp f hf L, first_precomp f hf L, first_precomp f hf L]
  have h0 : L (0,0) = 0 := L.map_zero
  rw [h0]
  norm_num [Fin.sum_univ_three, KPContFlatCuspCasimirSpecialization.coordinateDirection, L]
  ring

theorem product_energy_pullback (d : ℕ) (f : KPArch.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    productEnergy d f g = ∑ i : Fin d, ∑ j : Fin 3,
      ‖fderiv ℝ (fun y => f (KPArch.productAction d g y)) 0
        (KPContFlatCuspCasimirSpecialization.coordinateDirection d i j)‖^2 := by
  have he : productEnergy d (fun y => f (KPArch.productAction d g y)) (fun _ => 1) =
      productEnergy d f g := by
    unfold productEnergy
    apply Finset.sum_congr rfl
    intro i _
    have he (a : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
        KPArch.productAction d g
          (fun k => KPArch.action (Function.update (fun _ : Fin d => (1 : Matrix.GeneralLinearGroup (Fin 2) ℂ)) i a k) (0,0)) =
        fun k => KPArch.action (Function.update g i (g i * a) k) (0,0) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp only [KPArch.productAction, Function.update_self]
        exact (KPArch.action_laws (g i) a (0,0)).2.symm
      · simp only [KPArch.productAction, Function.update_of_ne hk,
          (KPArch.action_laws 1 1 (0,0)).1]
    simp_rw [he]
    exact (localEnergy_left
      (fun a => f (fun k => KPArch.action (Function.update g i a k) (0,0))) (g i) 1).trans
      (by rw [mul_one])
  rw [← he]
  have hb := product_basepoint_energy d (f ∘ KPArch.productAction d g)
    (hf.comp ((KPArch.productAction_contDiff d g).of_le (by simp)))
  exact hb

open _root_.DedekindZetaZeroFree.KPContThreeL2CotangentHelpers renaming arch_coframe_norm → arch_coframe_norm
open _root_.DedekindZetaZeroFree.KPContThreeL2CotangentHelpers renaming differential_norm_isometry → differential_norm_isometry
open _root_.DedekindZetaZeroFree.KPContArchLaplacianNaturality renaming act → act
open _root_.DedekindZetaZeroFree.KPContArchLaplacianNaturality renaming act_smooth → act_smooth
open _root_.DedekindZetaZeroFree.KPContArchLaplacianNaturality renaming act_metric → act_metric

private theorem coframe_norm_A (d : ℕ) (f : KPArch.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : KPArch.Space d) :
    (∑ i, ∑ j, ‖HyperbolicChart.differential d (f ∘ CotangentLogCoframe.A d)
      ((CotangentLogCoframe.A d).symm z) i j‖^2) =
      KPContActualChamberOutgoingAdapter.covariantNorm d 1 f z ^ 2 := by
  have ha : KPMeanZeroWeightedEnergy.archCoordinates d = CotangentLogCoframe.A d := by
    funext x
    funext i
    apply Prod.ext
    · simp [CotangentLogCoframe.A_apply, KPMeanZeroWeightedEnergy.archCoordinates,
        Complex.mk_eq_add_mul_I, mul_comm]
    · rfl
  have hr : KPMeanZeroWeightedEnergy.realCoordinates d z = (CotangentLogCoframe.A d).symm z := by
    apply (CotangentLogCoframe.A d).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    funext i
    apply Prod.ext
    · simpa [CotangentLogCoframe.A_apply, KPMeanZeroWeightedEnergy.realCoordinates, mul_comm]
        using Complex.re_add_im (z i).1
    · rfl
  simpa only [ha, hr] using arch_coframe_norm d f hf z

 theorem covariantNorm_pullback (d : ℕ) (f : KPArch.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : KPArch.Space d) :
    KPContActualChamberOutgoingAdapter.covariantNorm d 1
      (fun y => f (KPArch.productAction d g y)) z ^ 2 =
    KPContActualChamberOutgoingAdapter.covariantNorm d 1 f (KPArch.productAction d g z) ^ 2 := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun y => f (KPArch.productAction d g y)) :=
    hf.comp ((KPArch.productAction_contDiff d g).of_le (by simp))
  rw [← coframe_norm_A d _ hp, ← coframe_norm_A d f hf]
  have he : (f ∘ CotangentLogCoframe.A d) ∘ act d g =
      (fun y => f (KPArch.productAction d g y)) ∘ CotangentLogCoframe.A d := by
    funext x
    simp [act, Function.comp_def]
  have hx : act d g ((CotangentLogCoframe.A d).symm z) =
      (CotangentLogCoframe.A d).symm (KPArch.productAction d g z) := by
    simp [act]
  have hd := differential_norm_isometry d (act d g) ((CotangentLogCoframe.A d).symm z)
    ((act_smooth d g).differentiable (by simp) _) (act_metric d g _)
    (f ∘ CotangentLogCoframe.A d) ((hf.comp (CotangentLogCoframe.A d).contDiff).differentiable (by simp) _)
  simpa only [he, hx] using hd

private theorem basepoint_norm (d : ℕ) (f : KPArch.Space d → ℂ) :
    KPContActualChamberOutgoingAdapter.covariantNorm d 1 f 0 ^ 2 =
      ∑ i : Fin d, ∑ j : Fin 3,
        ‖fderiv ℝ f 0 (KPContFlatCuspCasimirSpecialization.coordinateDirection d i j)‖^2 := by
  simp only [KPContActualChamberOutgoingAdapter.covariantNorm]
  simp only [show ¬((1 : Fin 3) = 0) from by decide, ite_false, ite_true]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  norm_num [Fin.sum_univ_three, KPContActualChamberOutgoingAdapter.frameDerivative, KPArch.height,
    KPContActualSphericalFlatStage.coordinateDirection, KPContFlatCuspCasimirSpecialization.coordinateDirection]
  ring

 theorem product_energy (d : ℕ) (f : KPArch.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    productEnergy d f g = KPContActualChamberOutgoingAdapter.covariantNorm d 1 f
      (fun i => KPArch.action (g i) (0,0)) ^ 2 := by
  rw [product_energy_pullback d f hf g, ← basepoint_norm]
  exact covariantNorm_pullback d f hf g 0

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric

end
