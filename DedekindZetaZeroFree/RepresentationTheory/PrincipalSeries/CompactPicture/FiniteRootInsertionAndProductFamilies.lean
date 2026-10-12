module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.FinitePolarizedCharacters

@[expose] public section

section
noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPLiteralScalarHCFiniteRoot
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCFiniteInsertion
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def finiteRootAdele (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (u : q.adicCompletion F) : KPGlobalTorusFunctionData.Adeles F :=
  (0, RestrictedProduct.single (fun r : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
    r.adicCompletionIntegers F) q u)
theorem finiteRootAdele_eval (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (u : q.adicCompletion F) :
    adeleEval F (Sum.inr q) (finiteRootAdele F q u) = u := by
  change Pi.single q u q = u
  exact Pi.single_eq_same q u
theorem finiteRootAdele_eval_other (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (u : q.adicCompletion F) (v : KPHilbert.Place F) (hv : v ≠ Sum.inr q) :
    adeleEval F v (finiteRootAdele F q u) = 0 := by
  cases v with
  | inl w => rfl
  | inr r =>
    have hr : r ≠ q := by intro h; apply hv; exact congrArg Sum.inr h
    change Pi.single q u r = 0
    exact Pi.single_eq_of_ne hr u
theorem finiteInsertion_root (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (u : q.adicCompletion F) :
    (finiteInsertion F ζ hζ q (KPPGLLocalCover.N F ζ hζ (Sum.inr q) u)).val =
      KPGlobalTorusFunctionData.N F ζ hζ (finiteRootAdele F q u) := by
  rw [finiteInsertion_value]
  change finiteGroupInsertion F ζ hζ q
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) u)) = _
  rw [finiteGroupInsertion_raw]
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ _) =
    scalarQuotient F ζ hζ (amalgamation F ζ hζ _)
  congr 2
  apply RestrictedProduct.ext
  intro v
  by_cases hv : v = Sum.inr q
  · subst v
    simp [localToRestricted, KPGlobalTorusFunctionData.rootTuple,
      RestrictedProduct.coe_mulSingle_apply]
    rw [finiteRootAdele_eval]
  · simp [localToRestricted, KPGlobalTorusFunctionData.rootTuple,
      finiteRootAdele_eval_other F q u v hv, RestrictedProduct.coe_mulSingle_apply, hv,
      KPStandardLocalRootLifts.N_zero]
theorem canonical_root_eq (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q)
    (u : q.adicCompletion F) :
    (S.borel.upperRoot (Multiplicative.ofAdd u) : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) u :=
  (S.openCell S.polarization).upper_eq u

theorem finiteInsertion_canonical_root
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q)
    (u : q.adicCompletion F) :
    (finiteInsertion F ζ hζ q
      (S.borel.upperRoot (Multiplicative.ofAdd u))).val =
      KPGlobalTorusFunctionData.N F ζ hζ (finiteRootAdele F q u) := by
  rw [canonical_root_eq, finiteInsertion_root]

variable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
variable (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K)
open KPLiteralScalarHCLocalCovariance
open KPLiteralScalarHCCompactOrbit

end DedekindZetaZeroFree.KPLiteralScalarHCFiniteRoot

end

end

section
noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option warn.classDefReducibility false
namespace DedekindZetaZeroFree.KPLiteralScalarHCFiniteProduct
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCFiniteInsertion
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] pglLocalTopology localTopology

theorem finiteInsertion_commute
    (q r : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hqr : q ≠ r)
    (a : KPLocalExceptionalConstruction.ActualCover F ζ hζ q)
    (b : KPLocalExceptionalConstruction.ActualCover F ζ hζ r) :
    Commute (finiteInsertion F ζ hζ q a) (finiteInsertion F ζ hζ r b) := by
  apply Subtype.ext
  change (finiteGroupInsertion F ζ hζ q a) * (finiteGroupInsertion F ζ hζ r b) =
    (finiteGroupInsertion F ζ hζ r b) * (finiteGroupInsertion F ζ hζ q a)
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      change finiteGroupInsertion F ζ hζ q
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) a) *
        finiteGroupInsertion F ζ hζ r (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr r) b) =
        finiteGroupInsertion F ζ hζ r (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr r) b) *
        finiteGroupInsertion F ζ hζ q (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) a)
      rw [finiteGroupInsertion_raw, finiteGroupInsertion_raw]
      have hc : Commute (localToRestricted F ζ hζ (Sum.inr q) a)
          (localToRestricted F ζ hζ (Sum.inr r) b) := by
        change _ * _ = _ * _
        apply RestrictedProduct.ext
        intro v
        by_cases hvq : v = Sum.inr q
        · subst v
          simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply, hqr]
        · by_cases hvr : v = Sum.inr r
          · subst v
            simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply, hqr.symm]
          · simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply, hvq, hvr]
      exact (hc.map ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ))).eq

variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
abbrev FiniteProductCover := ∀ q : S, KPLocalExceptionalConstruction.ActualCover F ζ hζ q.val

def finiteProductInsertion : FiniteProductCover F ζ hζ S →*
    KPGlobalTorusFunctionData.finitePart F ζ hζ :=
  MonoidHom.noncommPiCoprod (fun q : S => finiteInsertion F ζ hζ q.val)
    (fun q r hqr => finiteInsertion_commute F ζ hζ q.val r.val
      (fun h => hqr (Subtype.ext h)))

@[simp] theorem finiteProductInsertion_single (q : S)
    (a : KPLocalExceptionalConstruction.ActualCover F ζ hζ q.val) :
    finiteProductInsertion F ζ hζ S (Pi.mulSingle q a) = finiteInsertion F ζ hζ q.val a :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

def productInsertionLevel (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    OpenSubgroup (FiniteProductCover F ζ hζ S) where
  toSubgroup := Subgroup.pi Set.univ (fun q => (insertionLevel F ζ hζ J q.val).toSubgroup)
  isOpen' := isOpen_set_pi Set.finite_univ (fun q _ => (insertionLevel F ζ hζ J q.val).isOpen)

theorem finiteProductInsertion_mem_level (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (j : FiniteProductCover F ζ hζ S) (hj : j ∈ productInsertionLevel F ζ hζ S J) :
    finiteProductInsertion F ζ hζ S j ∈ J.toOpenSubgroup := by
  change Finset.univ.noncommProd (fun q : S => finiteInsertion F ζ hζ q.val (j q))
    (fun q _ r _ hqr => finiteInsertion_commute F ζ hζ q.val r.val
      (fun h => hqr (Subtype.ext h)) (j q) (j r)) ∈ J.toOpenSubgroup
  apply Finset.noncommProd_induction
    (p := fun a => a ∈ J.toOpenSubgroup)
  · exact fun a b ha hb => J.toOpenSubgroup.mul_mem ha hb
  · exact J.toOpenSubgroup.one_mem
  · intro q _
    exact hj q (Set.mem_univ q)

variable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
variable (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K)
open KPLiteralScalarHCCompactOrbit
open KPLiteralScalarHCSliceCharts

end DedekindZetaZeroFree.KPLiteralScalarHCFiniteProduct

end

end

section
noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPLiteralScalarHCFiniteOutside
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCFiniteInsertion
open KPLiteralScalarHCFiniteProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

def rawOutsideStage : Subgroup (RestrictedCover F ζ hζ) :=
  (⨅ w : InfinitePlace F, (RestrictedProduct.evalMonoidHom
    (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v) (Sum.inl w)).ker) ⊓
  (⨅ q : T, (RestrictedProduct.evalMonoidHom
    (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v) (Sum.inr q.val)).ker)

def outsideStage : Subgroup (KPGlobalTorusFunctionData.finitePart F ζ hζ) :=
  ((rawOutsideStage F ζ hζ T).map
    ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ))).comap
    (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype

theorem outsideStage_commute_local (b : outsideStage F ζ hζ T) (q : T)
    (a : KPLocalExceptionalConstruction.ActualCover F ζ hζ q.val) :
    Commute b.val (finiteInsertion F ζ hζ q.val a) := by
  obtain ⟨r, hr, he⟩ := b.property
  have hq : r (Sum.inr q.val) = 1 := Subgroup.mem_iInf.mp hr.2 q
  apply Subtype.ext
  change b.val.val * finiteGroupInsertion F ζ hζ q.val a =
    finiteGroupInsertion F ζ hζ q.val a * b.val.val
  change ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)) r = b.val.val at he
  rw [← he]
  induction a using QuotientGroup.induction_on with
  | H a =>
    change ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)) r *
      finiteGroupInsertion F ζ hζ q.val (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) a) =
      finiteGroupInsertion F ζ hζ q.val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) a) *
        ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)) r
    rw [finiteGroupInsertion_raw]
    have hc : Commute r (localToRestricted F ζ hζ (Sum.inr q.val) a) := by
      change _ * _ = _ * _
      apply RestrictedProduct.ext
      intro v
      by_cases hv : v = Sum.inr q.val
      · subst v
        change r (Sum.inr q.val) * _ = _ * r (Sum.inr q.val)
        simp [hq]
      · simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply, hv]
    exact (hc.map ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ))).eq

theorem outsideStage_commute_product (b : outsideStage F ζ hζ T)
    (a : FiniteProductCover F ζ hζ T) :
    Commute b.val (finiteProductInsertion F ζ hζ T a) := by
  change Commute b.val (Finset.univ.noncommProd
    (fun q : T => finiteInsertion F ζ hζ q.val (a q))
    (fun q _ r _ hqr => finiteInsertion_commute F ζ hζ q.val r.val
      (fun h => hqr (Subtype.ext h)) (a q) (a r)))
  apply Finset.noncommProd_induction
    (p := fun c => Commute b.val c)
  · exact fun x y hx hy => hx.mul_right hy
  · exact Commute.one_right _
  · exact fun q _ => outsideStage_commute_local F ζ hζ T b q (a q)

open KPLiteralScalarHCLocalCovariance

open KPLiteralScalarHCCompactOrbit KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
variable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
variable (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K)

open KPLiteralScalarHCFiniteRoot

end DedekindZetaZeroFree.KPLiteralScalarHCFiniteOutside

end

end
