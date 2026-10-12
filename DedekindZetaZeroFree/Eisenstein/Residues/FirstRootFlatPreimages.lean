module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteInsertions
public import DedekindZetaZeroFree.Eisenstein.Residues.FlatSectionNondegeneracy
public import DedekindZetaZeroFree.Eisenstein.Residues.UpperRootPreimages

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources
open KPLiteralRaw hiding G Functions
open KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem finiteInjection_mem_finite (p : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) :
    finiteInjection R p a ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F R.A.zeta12 R.A.primitive_zeta12 := by
  apply Subgroup.mem_map.mpr
  refine ⟨KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a,?_,rfl⟩
  intro w
  simp [KPAdelicCoverRestrictedProduct.localToRestricted]

theorem upperCurve_commute_finite (w : InfinitePlace F) (b : Bool) (t : ℝ)
    (p : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) :
    Commute (upperCurve R w b t) (finiteInjection R p a) := by
  rw [upper_native_curve]
  exact RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F R.A.zeta12 R.A.primitive_zeta12 _
    ⟨_,finiteInjection_mem_finite R p a⟩

theorem upperLieDerivative_finite_fixed (w : InfinitePlace F) (b : Bool) (f : Functions R)
    (p : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (hf : ∀ g, f (g * finiteInjection R p a) = f g) :
    ∀ g, upperLieDerivative R w b f (g * finiteInjection R p a) = upperLieDerivative R w b f g := by
  intro g
  change deriv _ 0 = deriv _ 0
  congr 1
  funext t
  change f ((g * finiteInjection R p a) * upperCurve R w b t) = f (g * upperCurve R w b t)
  rw [mul_assoc,(upperCurve_commute_finite R w b t p a).eq.symm,← mul_assoc,hf]

theorem firstRoot_local_flat (w : InfinitePlace F) (e : ℤ)
    (f : Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
    (Cf : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 f)
    (hflat : ∀ s g, f.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (f.val 0) g)
    (hext : ExteriorFixed R (f.val 0)) :
    ∃ (v : Flat F R.A.zeta12 R.A.primitive_zeta12
        (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
      (Cv : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 v),
      v.val 0 = ThetaExpansion.firstRootLocalDerivative R w e (f.val 0) ∧
      (∀ s g, v.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (v.val 0) g) ∧
      ExteriorFixed R (v.val 0) ∧
      Cv.numerator 0 = ThetaExpansion.firstRootLocalDerivative R w e (Cf.numerator 0) := by
  have h := fun b => upper_flat_residue R w b f Cf hflat
  choose v C hv0 hv hC using h
  let c : Bool → ℂ := fun b => (Complex.I * (4 * Real.pi : ℂ))⁻¹ *
    (if b then (if e = 1 then -Complex.I else Complex.I) else 1)
  let z := FiniteWhittakerProjectors.FlatFiniteSum.sum F R.A.zeta12 R.A.primitive_zeta12 Finset.univ c v
  have hK := PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12
  let Cz := Classical.choice (flatScalarResidue_nonempty F R.A.zeta12 R.A.primitive_zeta12 _ hK z)
  have hval (s) (g) : z.val s g = ∑ b, c b * (v b).val s g := FiniteWhittakerProjectors.FlatFiniteSum.sum_val _ _ _ _ _ _ _ _
  have hzero : z.val 0 = ThetaExpansion.firstRootLocalDerivative R w e (f.val 0) := by
    funext g
    simp only [hval,hv0,Fintype.sum_bool,c,ThetaExpansion.firstRootLocalDerivative,
      Pi.smul_apply,Pi.add_apply,smul_eq_mul,Bool.false_eq_true,if_false,if_true,mul_one]
    ring
  refine ⟨z,Cz,hzero,?_,?_,?_⟩
  · intro s g
    rw [hval]
    simp_rw [hv]
    simp only [scalarWeight]
    rw [hval]
    simp only [scalarWeight,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro p hp a ha g
    rw [hval,hval]
    apply Finset.sum_congr rfl
    intro b _
    rw [hv0,upperLieDerivative_finite_fixed R w b _ p a (hext p hp a ha)]
  · funext g
    rw [flat_sum_residue hK Finset.univ c v Cz C]
    simp only [hC,Fintype.sum_bool,c,ThetaExpansion.firstRootLocalDerivative,
      Pi.smul_apply,Pi.add_apply,smul_eq_mul,Bool.false_eq_true,if_false,if_true,mul_one]
    ring

theorem firstRoot_word_flat (l : List (InfinitePlace F)) (e : InfinitePlace F → ℤ)
    (f : Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
    (Cf : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 f)
    (hflat : ∀ s g, f.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (f.val 0) g)
    (hext : ExteriorFixed R (f.val 0)) :
    ∃ (v : Flat F R.A.zeta12 R.A.primitive_zeta12
        (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
      (Cv : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 v),
      v.val 0 = l.foldr (fun w h => ThetaExpansion.firstRootLocalDerivative R w (e w) h) (f.val 0) ∧
      (∀ s g, v.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (v.val 0) g) ∧
      ExteriorFixed R (v.val 0) ∧
      Cv.numerator 0 = l.foldr (fun w h => ThetaExpansion.firstRootLocalDerivative R w (e w) h) (Cf.numerator 0) := by
  induction l with
  | nil => exact ⟨f,Cf,rfl,hflat,hext,rfl⟩
  | cons w l ih =>
    obtain ⟨v,Cv,hv0,hv,hextv,hC⟩ := ih
    obtain ⟨z,Cz,hz0,hz,hextz,hCz⟩ := firstRoot_local_flat R w (e w) v Cv hv hextv
    exact ⟨z,Cz,by simpa only [List.foldr_cons,hv0] using hz0,hz,hextz,
      by simpa only [List.foldr_cons,hC] using hCz⟩

theorem firstRoot_sources (Q₀ : AdmissibleFlatSources R) (T : Realization R Q₀)
    (B : ThetaExpansion.FirstRootCutoffs R) :
    ∃ Q : AdmissibleFlatSources R, Q.dq = Q₀.dq ∧
      ∀ v, ∃ C : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (Q.flat v),
        C.numerator 0 = ThetaExpansion.firstRootDerivatives R B (T.theta v) := by
  have hcan := fun v => canonical_flat_residue F R.A.zeta12 R.A.primitive_zeta12 Q₀.iwasawa
    (Q₀.flat v) (realizationScalarResidue T v)
  choose f Cf hf hCf using hcan
  have hf0 (v) : (f v).val 0 = (Q₀.flat v).val 0 := by
    funext g
    simp [hf]
  have hflat (v s g) : (f v).val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s ((f v).val 0) g := by
    rw [hf0,hf]
    rfl
  have hext (v) : ExteriorFixed R ((f v).val 0) := by
    rw [hf0]
    exact Q₀.exterior_spherical v 0
  have hword := fun v => firstRoot_word_flat R (Finset.univ : Finset (InfinitePlace F)).toList
    B.exponent (f v) (Cf v) (hflat v) (hext v)
  choose z Cz hz0 hz hextz hCz using hword
  letI := Q₀.finite_companions
  obtain ⟨V,hV⟩ := FiniteWhittakerProjectors.canonical_family_level R z hz
  let Q : AdmissibleFlatSources R := {
    K := (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K
    iwasawa := PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12
    flat := z
    finite_companions := Q₀.finite_companions
    level := V
    common_level := hV
    ordinary := ?_
    exterior_spherical := ?_
    dq := Q₀.dq
    quotientHaar := Q₀.quotientHaar
    probability := Q₀.probability }
  · refine ⟨Q,rfl,?_⟩
    intro v
    refine ⟨Cz v,?_⟩
    change (Cz v).numerator 0 = _
    have hp : (Cf v).numerator 0 = T.theta v := funext (hCf v)
    simpa only [hp,ThetaExpansion.firstRootDerivatives] using hCz v
  · intro v s ε g
    exact ThetaExpansion.induced_ordinary_central_covariance R s _ ((z v).property.1 s) ε g
  · intro v s p hp a ha g
    rw [hz,hz]
    change Complex.exp _ * (z v).val 0 (g * finiteInjection R p a) =
      Complex.exp _ * (z v).val 0 g
    rw [hextz v p hp a ha]
    have hα := KPContFlatFullProductIwasawa.alpha_mul_compact F R.A.zeta12 R.A.primitive_zeta12 g
      ⟨finiteInjection R p a,finiteInjection_compact_mem R p a ha⟩
    change KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 (g * finiteInjection R p a) =
      KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 g at hα
    change Complex.exp (s * (KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12
      (g * finiteInjection R p a) : ℂ)) * (z v).val 0 g =
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 g : ℂ)) * (z v).val 0 g
    rw [hα]

end DedekindZetaZeroFree.RootDerivatives

end
