module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FlatProjection
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FrozenProjectorFamily

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
variable (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F)

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end

section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
variable (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F)

theorem flat_root_word_lift {K : Subgroup (Group R)}
    (hK : KPLiteralRaw.IwasawaCompact F R.A.zeta12 R.A.primitive_zeta12 K)
    (f : KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 K)
    (A : _root_.DedekindZetaZeroFree.RootDerivatives.FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 f) (l : List R.A.Sf) :
    ∃ (v : KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 K)
      (B : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 v),
      (v.val 0 = FiniteWhittakerProjectors.rootProjectorWord R I c t l (f.val 0)) ∧
      B.numerator 0 = FiniteWhittakerProjectors.rootProjectorWord R I c t l (A.numerator 0) := by
  induction l with
  | nil => exact ⟨f,A,rfl,rfl⟩
  | cons q l ih =>
    obtain ⟨v,B,hv,hB⟩ := ih
    obtain ⟨w,C,hw,hC⟩ := flat_local_sum_residue hK B q.val Finset.univ (c q)
      (fun i => KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) (t q i))
    refine ⟨w,C,?_,?_⟩
    · funext g
      rw [hw]
      simp_rw [ExteriorWhittakerValues.StoredWhittaker.finite_root_injection R]
      change (∑ i, c q i * v.val 0 (g * FiniteWhittakerProjectors.finiteRoot R q.val (t q i))) = _
      rw [hv]
      simp only [FiniteWhittakerProjectors.rootProjectorWord, List.foldr_cons, LinearMap.comp_apply,
        FiniteWhittakerProjectors.rightTranslateSum_apply]
    · funext g
      rw [hC]
      simp_rw [ExteriorWhittakerValues.StoredWhittaker.finite_root_injection R]
      change (∑ i, c q i * B.numerator 0 (g * FiniteWhittakerProjectors.finiteRoot R q.val (t q i))) = _
      rw [hB]
      simp only [FiniteWhittakerProjectors.rootProjectorWord, List.foldr_cons, LinearMap.comp_apply,
        FiniteWhittakerProjectors.rightTranslateSum_apply]

theorem selected_root_word_flat_lifts {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (l : List R.A.Sf) :
    ∃ (f : R.A.UnitQuotient → KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 A.sources.K)
      (B : ∀ v, FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (f v)),
      (∀ v, (f v).val 0 = FiniteWhittakerProjectors.rootProjectorWord R I c t l ((A.sources.flat v).val 0)) ∧
      ∀ v, (B v).numerator 0 = FiniteWhittakerProjectors.rootProjectorWord R I c t l (A.realization.theta v) := by
  have he := fun v => flat_root_word_lift R I c t A.sources.iwasawa
    (A.sources.flat v) (realizationScalarResidue A.realization v) l
  choose f B hf hB using he
  exact ⟨f,B,hf,hB⟩

end DedekindZetaZeroFree.RootDerivatives

end
end
