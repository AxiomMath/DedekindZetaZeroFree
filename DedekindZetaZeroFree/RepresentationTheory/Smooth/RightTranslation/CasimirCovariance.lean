module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DifferentialWords.KFiniteVectors
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CasimirMatrixTranslation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.ResidualFullGroupTranslation
open KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming slice_smooth → slice_smooth
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming slice_slot_omega → slice_slot_omega
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming slotCasimir → slotCasimir
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming productCasimir → productCasimir
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming productWord_congr → productWord_congr
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming matrixPullback_casimir_units → matrixPullback_casimir_units
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming invertibleProducts_open → invertibleProducts_open
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming matrixPullback_at_units → matrixPullback_at_units
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming rightOmega → rightOmega
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "MP" => MatrixProduct F
local notation "O" => invertibleProducts (F := F)
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ

 def rightProduct (k : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (m : MP) : MP := fun v => m v * (k v).val

private theorem rightProduct_mem (k : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (m : MP) (hm : m ∈ O) : rightProduct k m ∈ O := by
  intro v
  simp only [rightProduct, Matrix.det_mul]
  exact mul_ne_zero (hm v) (Matrix.GeneralLinearGroup.det_ne_zero (k v))

private theorem rightProduct_smooth (k : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    ContDiff ℝ (⊤ : ℕ∞) (rightProduct k) := by
  apply contDiff_pi.mpr; intro v
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  simp only [rightProduct, Matrix.mul_apply]
  fun_prop

private theorem product_translate (f : MP → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (k : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (m : MP) (hm : m ∈ O) :
    productCasimir (fun a => f (rightProduct k a)) m = productCasimir f (rightProduct k m) := by
  have hm' := rightProduct_mem k m hm
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun a => f (rightProduct k a)) O :=
    hf.comp (rightProduct_smooth k).contDiffOn (fun a ha => rightProduct_mem k a ha)
  unfold productCasimir
  apply Finset.sum_congr rfl
  intro v _
  have hleft := slice_slot_omega v (fun a => f (rightProduct k a)) m hm hs (m v) (hm v)
  have hright := slice_slot_omega v f (rightProduct k m) hm' hf (rightProduct k m v) (hm' v)
  simp only [Function.update_eq_self] at hleft hright
  rw [hleft, hright]
  have he : (fun a => f (rightProduct k (Function.update m v a))) =
      fun a => f (Function.update (rightProduct k m) v (a * (k v).val)) := by
    funext a
    apply congrArg f
    funext w
    by_cases hw : w = v <;> simp [rightProduct, hw]
  rw [he]
  apply congrArg (fun z : ℂ => -((1 : ℂ)/2) * z)
  exact ResidualMatrixTranslation.matrix_casimir_right_translate
    (fun a => f (Function.update (rightProduct k m) v a))
    {a | a.det ≠ 0} (isOpen_ne.preimage (by fun_prop))
    (slice_smooth v (rightProduct k m) hm' f hf)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero (m v) (hm v)) (k v) (hm' v)

private theorem product_congr {f h : MP → ℂ} (he : Set.EqOn f h O)
    (m : MP) (hm : m ∈ O) : productCasimir f m = productCasimir h m := by
  unfold productCasimir slotCasimir
  apply Finset.sum_congr rfl
  intro v _
  have h2 (i j : Fin 6) := productWord_congr [(v,i),(v,j)] he hm
  simp only [productRightWord] at h2
  simp_rw [h2]

 theorem casimir_right_translate_of_product
    (e : (KPSmoothActualFlowData.GInfinity F × KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ) ≃ₜ* G)
    (he : ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val)
    (f : G → ℂ) (hf : RawWordKFinite.NativeSmooth f) (g k : G) :
    KPMsGreenFlux.casimir F ζ hζ (fun a => f (a*k)) g =
      KPMsGreenFlux.casimir F ζ hζ f (g*k) := by
  let b := (e.symm k).1
  let c := (e.symm k).2
  let κ : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun v => (b v).out
  let ins := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
  have hb : (fun v => Matrix.ProjGenLinGroup.mk (κ v)) = b := by
    funext v
    exact Quotient.out_eq _
  have hin1 : ins 1 = 1 := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1
  have hinmul (x y : KPSmoothActualFlowData.GInfinity F) : ins (x*y) = ins x * ins y :=
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1 x y
  have hearch (a : KPSmoothActualFlowData.GInfinity F) : e (a,1) = ins a := by
    rw [he]; simp [ins]
  have hefinite : e (1,c) = c.val := by
    rw [he]; change ins 1 * c.val = c.val
    rw [hin1, one_mul]
  have hcomm (a : KPSmoothActualFlowData.GInfinity F) : ins a * c.val = c.val * ins a := by
    rw [← hearch, ← hefinite, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  have hk : k = ins b * c.val := by
    have hh := e.apply_symm_apply k
    change e (b,c) = k at hh
    rw [he] at hh
    exact hh.symm
  have heq : Set.EqOn (matrixPullback (fun a => f (a*k)) g)
      (fun m => matrixPullback f (g*c.val) (rightProduct κ m)) O := by
    intro m hm
    let A : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 :=
      fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero (m v) (hm v)
    change matrixPullback (fun a => f (a*k)) g (fun v => (A v).val) =
      matrixPullback f (g*c.val) (fun v => (A v * κ v).val)
    rw [matrixPullback_at_units, matrixPullback_at_units]
    have hprod : (fun v => Matrix.ProjGenLinGroup.mk (A v * κ v)) =
        (fun v => Matrix.ProjGenLinGroup.mk (A v)) * b := by
      funext v
      rw [map_mul]
      change _ * Matrix.ProjGenLinGroup.mk (κ v) = _ * b v
      rw [congrFun hb v]
    rw [hprod]
    change f ((g * ins (fun v => Matrix.ProjGenLinGroup.mk (A v))) * k) =
      f ((g*c.val) * ins ((fun v => Matrix.ProjGenLinGroup.mk (A v)) * b))
    rw [hk]
    apply congrArg f
    calc
      _ = g * ((ins (fun v => Matrix.ProjGenLinGroup.mk (A v)) * ins b) * c.val) := by
        simp only [mul_assoc]
      _ = g * (ins ((fun v => Matrix.ProjGenLinGroup.mk (A v)) * b) * c.val) := by
        rw [hinmul]
      _ = g * (c.val * ins ((fun v => Matrix.ProjGenLinGroup.mk (A v)) * b)) := by
        rw [hcomm]
      _ = _ := by simp only [mul_assoc]
  let oneProducts : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun _ => 1
  have h1 (q : G → ℂ) : matrixPullback q g (fun v => (oneProducts v).val) = q g := by
    rw [matrixPullback_at_units]
    have hmap : (fun v => Matrix.ProjGenLinGroup.mk (oneProducts v)) = 1 := by
      funext v; simp [oneProducts]
    rw [hmap]
    change q (g * ins 1) = q g
    rw [hin1, mul_one]
  have hone : (fun v => (oneProducts v).val) ∈ O := fun v => Matrix.GeneralLinearGroup.det_ne_zero _
  rw [← h1 (KPMsGreenFlux.casimir F ζ hζ (fun a => f (a*k))), matrixPullback_casimir_units]
  rw [product_congr heq _ hone, product_translate _ (matrixPullback_smooth f hf (g*c.val)) κ _ hone]
  have ht : rightProduct κ (fun v => (oneProducts v).val) = fun v => (κ v).val := by
    funext v; simp [rightProduct, oneProducts]
  rw [ht, ← matrixPullback_casimir_units, matrixPullback_at_units, hb]
  change KPMsGreenFlux.casimir F ζ hζ f ((g*c.val) * ins b) = _
  rw [mul_assoc, ← hcomm, ← hk]

theorem casimir_right_translate (f : G → ℂ) (hf : RawWordKFinite.NativeSmooth f) (g k : G) :
    KPMsGreenFlux.casimir F ζ hζ (fun a => f (a*k)) g =
      KPMsGreenFlux.casimir F ζ hζ f (g*k) := by
  obtain ⟨e,he⟩ := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_product_splitting F ζ hζ
  exact casimir_right_translate_of_product e he f hf g k

end DedekindZetaZeroFree.FourierContinuation.ResidualFullGroupTranslation

end
