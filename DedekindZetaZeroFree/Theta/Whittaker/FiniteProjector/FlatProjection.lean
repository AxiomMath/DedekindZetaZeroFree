module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FlatResidue
public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter MeasureTheory
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open KPLiteralRaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem flat_sum_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) {I : Type} (s : Finset I)
    (c : I → ℂ) (f : I → Flat F ζ hζ K)
    (A : FlatScalarResidue F ζ hζ (FlatFiniteSum.sum F ζ hζ s c f))
    (B : ∀ i, FlatScalarResidue F ζ hζ (f i)) (g : G F ζ hζ) :
    A.numerator 0 g = ∑ i ∈ s, c i * (B i).numerator 0 g := by
  simpa only [mul_one] using flat_finite_residue hK A s f B (fun i _ => c i)
    (fun _ _ => analyticOnNhd_const) 1
    (fun z g => by simpa using FlatFiniteSum.sum_val F ζ hζ s c f z g) g

open MomentSources
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def realizationScalarResidue {R : PrincipalMellin.ActualRecipe S η}
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (v : R.A.UnitQuotient) :
    FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (Q.flat v) where
  E := fun z => T.E v z
  meromorphic := T.meromorphic v
  chamber := T.chamber v
  radius := T.radius
  radius_pos := T.radius_pos
  numerator := T.cleared v
  analytic := T.analytic v
  clears := by
    intro g
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos),
      self_mem_nhdsWithin] with z hz hn
    exact congrFun (T.clears v z hz hn) g

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end

section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem flatScalarResidue_nonempty (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    Nonempty (FlatScalarResidue F ζ hζ f) := by
  letI : T2Space (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨C, _⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨Haar, _, _, P, ⟨H⟩⟩ := kp_ms_fixed_haar_disintegration F ζ hζ
    (Measure.haar : Measure (G F ζ hζ)) inferInstance
  exact flatScalarResidue_exists F ζ hζ C Haar P H K hK f

variable {F ζ hζ}

theorem flat_sum_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) {I : Type} (s : Finset I)
    (c : I → ℂ) (f : I → Flat F ζ hζ K)
    (A : FlatScalarResidue F ζ hζ (FiniteWhittakerProjectors.FlatFiniteSum.sum F ζ hζ s c f))
    (B : ∀ i, FlatScalarResidue F ζ hζ (f i)) (g : G F ζ hζ) :
    A.numerator 0 g = ∑ i ∈ s, c i * (B i).numerator 0 g := by
  simpa only [mul_one] using flat_finite_residue hK A s f B (fun i _ => c i)
    (fun _ _ => analyticOnNhd_const) 1
    (fun z g => by simpa using FiniteWhittakerProjectors.FlatFiniteSum.sum_val F ζ hζ s c f z g) g

theorem flat_translate_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) {f : Flat F ζ hζ K}
    (A : FlatScalarResidue F ζ hζ f) (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    ∃ (v : Flat F ζ hζ K) (B : FlatScalarResidue F ζ hζ v),
      (∀ g, v.val 0 g = f.val 0 (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a))) ∧
      ∀ g, B.numerator 0 g = A.numerator 0
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) := by
  obtain ⟨v,n,b,w,hexp,hv,hv0⟩ := FiniteWhittakerProjectors.FlatFiniteSum.translate_lift F ζ hζ K hK f q a
  let B := Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK v)
  let C := fun i => Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK (w i))
  refine ⟨v,B,hv0,?_⟩
  intro g
  have hA := flat_finite_residue hK A Finset.univ w C
    (fun i z => Complex.exp (z * (b i : ℂ)))
    (fun i _ => (analyticOnNhd_id.mul analyticOnNhd_const).cexp)
    _ hexp g
  have hB := flat_finite_residue hK B Finset.univ w C (fun _ _ => 1)
    (fun _ _ => analyticOnNhd_const) 1 (fun z g => by
      simpa only [mul_one, one_mul] using hv z g) g
  simp only [mul_one, zero_mul, Complex.exp_zero, one_mul] at hA hB
  exact hB.trans hA.symm

theorem flat_local_sum_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) {f : Flat F ζ hζ K}
    (A : FlatScalarResidue F ζ hζ f) (q : KPFinitePlace F)
    {I : Type} (s : Finset I) (c : I → ℂ)
    (a : I → KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    ∃ (v : Flat F ζ hζ K) (B : FlatScalarResidue F ζ hζ v),
      (∀ g, v.val 0 g = ∑ i ∈ s, c i * f.val 0
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) (a i)))) ∧
      ∀ g, B.numerator 0 g = ∑ i ∈ s, c i * A.numerator 0
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) (a i))) := by
  have he := fun i => flat_translate_residue hK A q (a i)
  choose v B hv hB using he
  let w := FiniteWhittakerProjectors.FlatFiniteSum.sum F ζ hζ s c v
  let C := Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK w)
  refine ⟨w,C,?_,?_⟩
  · intro g
    simp only [w, FiniteWhittakerProjectors.FlatFiniteSum.sum_val, hv]
  · intro g
    rw [flat_sum_residue hK s c v C B]
    exact Finset.sum_congr rfl (fun i _ => congrArg (c i * ·) (hB i g))

open MomentSources
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def realizationScalarResidue {R : PrincipalMellin.ActualRecipe S η}
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (v : R.A.UnitQuotient) :
    FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (Q.flat v) where
  E := fun z => T.E v z
  meromorphic := T.meromorphic v
  chamber := T.chamber v
  radius := T.radius
  radius_pos := T.radius_pos
  numerator := T.cleared v
  analytic := T.analytic v
  clears := by
    intro g
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos),
      self_mem_nhdsWithin] with z hz hn
    exact congrFun (T.clears v z hz hn) g

end DedekindZetaZeroFree.RootDerivatives

end
end
