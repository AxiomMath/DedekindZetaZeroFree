module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DifferentialWords.KFiniteVectors

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageDescent
open KPContSectorCoveredQuotientVocabulary
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
local notation "G" => ActualCover F ζ hζ
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv → productEquiv
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv_apply → productEquiv_apply

def descend (f : G → ℂ)
    (hr : ∀ γ : Gamma F ζ hζ, ∀ g, f (γ.val*g) = f g)
    (hk : ∀ k : K_U F ζ hζ U, ∀ g, f (g*k.val) = f g) :
    CoveredSpherical F ζ hζ U → ℂ :=
  (Quotient.lift f (by
    intro a b hab
    obtain ⟨γ,hγ,k,hk',he⟩ := DoubleCoset.rel_iff.mp hab
    rw [he, hk ⟨k,hk'⟩, hr ⟨γ,hγ⟩])) ∘
      (KPContSectorQuotientRelationsComparison.e F ζ hζ U).symm

theorem descend_pin (f : G → ℂ)
    (hr : ∀ γ : Gamma F ζ hζ, ∀ g, f (γ.val*g) = f g)
    (hk : ∀ k : K_U F ζ hζ U, ∀ g, f (g*k.val) = f g) (g : G) :
    descend F ζ hζ U f hr hk
      (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) = f g := by
  simp only [descend, Function.comp_apply, KPContSectorQuotientRelationsComparison.piTilde,
    coveredActualMap_mk, Homeomorph.symm_apply_apply]
  rfl

theorem descend_coefficient (f : G → ℂ)
    (hr : ∀ γ : Gamma F ζ hζ, ∀ g, f (γ.val*g) = f g)
    (hk : ∀ k : K_U F ζ hζ U, ∀ g, f (g*k.val) = f g)
    (x : SymmetricSpace F) (c : FiniteCover F ζ hζ) :
    descend F ζ hζ U f hr hk (Quotient.mk (coveredRelation F ζ hζ U) (x,c)) =
      f (productEquiv F ζ hζ (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x,c)) := by
  have hp := descend_pin F ζ hζ U f hr hk
    (productEquiv F ζ hζ (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x,c))
  simp only [KPContSectorQuotientRelationsComparison.piTilde, Function.comp_apply,
    coveredActualMap_mk, productEquiv_apply, KPContSectorQuotientRelationsComparison.e_mk,
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection] at hp
  simpa only [productEquiv_apply] using hp
end DedekindZetaZeroFree.FourierContinuation.ResidualAverageDescent

namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageDescent
open KPContSectorCoveredQuotientVocabulary
open KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv → productEquiv
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv_apply → productEquiv_apply
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming diagonalUnit → diagonalUnit
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming matrixPullback_at_units → matrixPullback_at_units
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
local notation "G" => ActualCover F ζ hζ
 theorem descend_coefficient_smooth (f : G → ℂ)
    (hf : RawWordKFinite.NativeSmooth f)
    (hr : ∀ γ : Gamma F ζ hζ, ∀ g, f (γ.val*g) = f g)
    (hk : ∀ k : K_U F ζ hζ U, ∀ g, f (g*k.val) = f g)
    (c : FiniteCover F ζ hζ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F =>
      descend F ζ hζ U f hr hk (Quotient.mk (coveredRelation F ζ hζ U) (x,c))) := by
  let q : SymmetricSpace F → KPGlobalResidualConstruction.ArchCoordinates F := fun x w =>
    ![(x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).1,
      (Real.exp (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).2 : ℂ), 0]
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := by
    apply contDiff_pi.mpr; intro w
    apply contDiff_pi.mpr; intro i
    fin_cases i
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).1)
      fun_prop
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => (Real.exp (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).2 : ℂ))
      exact Complex.ofRealCLM.contDiff.comp ((show ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).2) from by fun_prop).exp)
    · exact contDiff_const
  have hqd : Set.MapsTo q Set.univ (KPGlobalResidualConstruction.archDomain F) := by
    intro x _ w
    change (Real.exp _ : ℂ) ≠ 0
    exact_mod_cast Real.exp_ne_zero _
  have hs := (hf (c : G)).comp hq.contDiffOn hqd
  apply contDiffOn_univ.mp
  apply hs.congr
  intro x _
  rw [descend_coefficient]
  have hpin : KPGlobalResidualConstruction.archChart F ζ hζ (q x) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x) := by
    rw [KPLiteralChamber.right_insertion]
    congr 1
    funext w
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (KPLiteralChamber.rightMatrix (q x w)).val i j =
      KPContSectorArchSphericalFibers.sectionMatrix F ζ hζ x w i j
    rw [KPContSectorArchSphericalFibers.sectionMatrix_formula]
    fin_cases i <;> fin_cases j <;>
      simp [KPLiteralChamber.rightMatrix, diagonalUnit, q,
        KubotaRankTwo.n, KubotaRankTwo.d, KPStandardLocalRootLifts.lowerN,
        Matrix.mul_apply, Fin.sum_univ_two, Real.exp_ne_zero]
  change f (productEquiv F ζ hζ (_,c)) = f ((c : G) * KPGlobalResidualConstruction.archChart F ζ hζ (q x))
  rw [hpin]
  have he := (productEquiv F ζ hζ).map_mul
    ((1 : KPSmoothActualFlowData.GInfinity F), c)
    (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x, 1)
  change productEquiv F ζ hζ ((1, c) * (_, 1)) =
    productEquiv F ζ hζ (1,c) * productEquiv F ζ hζ (_,1) at he
  simp only [Prod.mk_mul_mk, one_mul, mul_one, productEquiv_apply,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1,
    one_mul, OneMemClass.coe_one, mul_one] at he
  simpa only [productEquiv_apply, KPContSectorArchSphericalFibers.iwasawaSection] using congrArg f he
end DedekindZetaZeroFree.FourierContinuation.ResidualAverageDescent

namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageDescent
open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv → productEquiv
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv_apply → productEquiv_apply
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
local notation "G" => ActualCover F ζ hζ

def genuineDescent (f : G → ℂ)
    (hr : ∀ γ : Gamma F ζ hζ, ∀ g, f (γ.val*g) = f g)
    (hk : ∀ k : K_U F ζ hζ U, ∀ g, f (g*k.val) = f g)
    (hc : ∀ ε g, f (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g) =
      (chi F ζ hζ ε : ℂ) * f g) : GenuineCoveredScalars F ζ hζ U :=
  ⟨descend F ζ hζ U f hr hk, by
    intro ε v
    refine Quotient.inductionOn v ?_
    rintro ⟨x,c⟩
    rw [z_mk, descend_coefficient, descend_coefficient]
    have hp := (productEquiv F ζ hζ).map_mul
      ((1 : KPSmoothActualFlowData.GInfinity F), KPCuspGenuineMonodromy.central F ζ hζ ε)
      (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x,c)
    change productEquiv F ζ hζ ((1,_) * (_,c)) =
      productEquiv F ζ hζ (1,_) * productEquiv F ζ hζ (_,c) at hp
    simp only [Prod.mk_mul_mk, one_mul] at hp
    rw [hp, productEquiv_apply]
    simp only [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, one_mul]
    exact hc ε _⟩

def smoothDescent (f : G → ℂ)
    (hf : RawWordKFinite.NativeSmooth f)
    (hr : ∀ γ : Gamma F ζ hζ, ∀ g, f (γ.val*g) = f g)
    (hk : ∀ k : K_U F ζ hζ U, ∀ g, f (g*k.val) = f g)
    (hc : ∀ ε g, f (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g) =
      (chi F ζ hζ ε : ℂ) * f g) : smoothCovered F ζ hζ U :=
  ⟨genuineDescent F ζ hζ U f hr hk hc, fun c =>
    descend_coefficient_smooth F ζ hζ U f hf hr hk c⟩
end DedekindZetaZeroFree.FourierContinuation.ResidualAverageDescent

end
