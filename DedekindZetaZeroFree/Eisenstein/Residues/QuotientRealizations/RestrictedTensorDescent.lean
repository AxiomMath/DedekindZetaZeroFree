module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorProducts.IntegralQuotientActions
public import DedekindZetaZeroFree.Eisenstein.Residues.RealizationAndPeriods
public import DedekindZetaZeroFree.Algebra.TensorProducts.SurjectiveMapKernels

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.DetectedDictionary
open MomentSources TensorActionSource
open _root_.DedekindZetaZeroFree.KPLiteralResidueKernelTests renaming tensor_kernel_le_span → tensor_kernel_le_span
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (M : ∀ q, LocalImageData R q)

theorem sourceStage_kernel_test
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Finset (KPHilbert.Place F))
    (L : RestrictedTensorSimple.Stage (plusLocal R M) s →ₗ[ℂ] V)
    (hlocal : ∀ (x : ∀ p : s, plusLocal R M p) (p : s),
      sourceQuotient R M p (x p) = 0 → L (PiTensorProduct.tprod ℂ x) = 0) :
    LinearMap.ker (sourceStageQuotient R M s) ≤ LinearMap.ker L := by
  have hk := tensor_kernel_le_span (fun p : s => sourceQuotient R M p)
    (fun p => sourceQuotient_surjective R M p)
  apply hk.trans
  apply Submodule.span_le.mpr
  rintro y ⟨x, ⟨p, hp⟩, rfl⟩
  exact hlocal x p hp

theorem sourceStage_descent
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Finset (KPHilbert.Place F))
    (L : RestrictedTensorSimple.Stage (plusLocal R M) s →ₗ[ℂ] V)
    (hlocal : ∀ (x : ∀ p : s, plusLocal R M p) (p : s),
      sourceQuotient R M p (x p) = 0 → L (PiTensorProduct.tprod ℂ x) = 0) :
    ∃! B : RestrictedTensorSimple.Stage (actualLocal R M) s →ₗ[ℂ] V,
      ∀ x, B (sourceStageQuotient R M s x) = L x := by
  obtain ⟨B, hB⟩ := KPLiteralResidueDescent.factor_through_surjection
    (sourceStageQuotient R M s) (sourceStageQuotient_surjective R M s) L
    (fun x hx => sourceStage_kernel_test R M s L hlocal hx)
  refine ⟨B, hB, ?_⟩
  intro C hC
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := sourceStageQuotient_surjective R M s y
  rw [hC, hB]

theorem sourceStageQuotient_transition
    (e : ∀ p, plusLocal R M p) (bad : Finset (KPHilbert.Place F))
    (s t : RestrictedTensorSimple.Level bad) (hst : s ≤ t) :
    (sourceStageQuotient R M t.val).comp
        (RestrictedTensorSimple.transition (plusLocal R M) e bad s t hst) =
      (RestrictedTensorSimple.transition (actualLocal R M)
          (fun p => sourceQuotient R M p (e p)) bad s t hst).comp
        (sourceStageQuotient R M s.val) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure,
    sourceStageQuotient, PiTensorProduct.map_tprod]
  congr 1
  funext p
  split_ifs <;> rfl

theorem descendedStage_compatible
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : ∀ p, plusLocal R M p) (bad : Finset (KPHilbert.Place F))
    (L : ∀ s : RestrictedTensorSimple.Level bad,
      RestrictedTensorSimple.Stage (plusLocal R M) s.val →ₗ[ℂ] V)
    (hL : ∀ s t (hst : s ≤ t) x,
      L t (RestrictedTensorSimple.transition (plusLocal R M) e bad s t hst x) = L s x)
    (B : ∀ s : RestrictedTensorSimple.Level bad,
      RestrictedTensorSimple.Stage (actualLocal R M) s.val →ₗ[ℂ] V)
    (hB : ∀ s x, B s (sourceStageQuotient R M s.val x) = L s x) :
    ∀ s t (hst : s ≤ t) x,
      B t (RestrictedTensorSimple.transition (actualLocal R M)
        (fun p => sourceQuotient R M p (e p)) bad s t hst x) = B s x := by
  intro s t hst y
  obtain ⟨x, rfl⟩ := sourceStageQuotient_surjective R M s.val y
  have he := LinearMap.congr_fun (sourceStageQuotient_transition R M e bad s t hst) x
  change sourceStageQuotient R M t.val
      (RestrictedTensorSimple.transition (plusLocal R M) e bad s t hst x) =
    RestrictedTensorSimple.transition (actualLocal R M)
      (fun p => sourceQuotient R M p (e p)) bad s t hst
      (sourceStageQuotient R M s.val x) at he
  rw [← he, hB, hL, hB]

theorem sourceCore_descent
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : ∀ p, plusLocal R M p) (bad : Finset (KPHilbert.Place F))
    (L : ∀ s : RestrictedTensorSimple.Level bad,
      RestrictedTensorSimple.Stage (plusLocal R M) s.val →ₗ[ℂ] V)
    (hL : ∀ s t (hst : s ≤ t) x,
      L t (RestrictedTensorSimple.transition (plusLocal R M) e bad s t hst x) = L s x)
    (hlocal : ∀ (s : RestrictedTensorSimple.Level bad)
      (x : ∀ p : s.val, plusLocal R M p) (p : s.val),
      sourceQuotient R M p (x p) = 0 → L s (PiTensorProduct.tprod ℂ x) = 0) :
    ∃! B : RestrictedTensorSimple.Core (actualLocal R M)
        (fun p => sourceQuotient R M p (e p)) bad →ₗ[ℂ] V,
      ∀ s x, B (RestrictedTensorSimple.stageInclusion (actualLocal R M)
        (fun p => sourceQuotient R M p (e p)) bad s
          (sourceStageQuotient R M s.val x)) = L s x := by
  have hd (s : RestrictedTensorSimple.Level bad) :=
    sourceStage_descent R M s.val (L s) (hlocal s)
  choose B hB huniq using hd
  have hcompat := descendedStage_compatible R M e bad L hL B hB
  let b : RestrictedTensorSimple.Core (actualLocal R M)
      (fun p => sourceQuotient R M p (e p)) bad →ₗ[ℂ] V :=
    Module.DirectLimit.lift ℂ (RestrictedTensorSimple.Level bad)
      (fun s => RestrictedTensorSimple.Stage (actualLocal R M) s.val)
      (RestrictedTensorSimple.transition (actualLocal R M)
        (fun p => sourceQuotient R M p (e p)) bad) B hcompat
  have hb (s : RestrictedTensorSimple.Level bad) x :
      b (RestrictedTensorSimple.stageInclusion (actualLocal R M)
        (fun p => sourceQuotient R M p (e p)) bad s x) = B s x :=
    Module.DirectLimit.lift_of B hcompat x
  refine ⟨b, fun s x => (hb s _).trans (hB s x), ?_⟩
  intro C hC
  apply LinearMap.ext
  intro y
  letI : Nonempty (RestrictedTensorSimple.Level bad) := ⟨⟨bad, le_rfl⟩⟩
  obtain ⟨s, x, rfl⟩ := Module.DirectLimit.exists_of y
  obtain ⟨z, rfl⟩ := sourceStageQuotient_surjective R M s.val x
  exact (hC s z).trans ((hb s _).trans (hB s z)).symm

end DedekindZetaZeroFree.FourierContinuation.DetectedDictionary

end
