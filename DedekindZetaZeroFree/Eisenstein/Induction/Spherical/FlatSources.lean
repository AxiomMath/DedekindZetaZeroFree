module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.ExteriorAveraging

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPLiteralRaw
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

 theorem normalized_spherical_flat_sources {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (D : ThetaExpansion.SphericalTransportData R A)
    (P : ThetaExpansion.NormalizedSphericalTensor R A D) :
    ∃ Q : AdmissibleFlatSources R, Q.dq = A.sources.dq ∧
      ∃ C : ∀ v, FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (Q.flat v),
        (∀ v, (C v).numerator 0 = tensorFunction R A.factorization D.tensor.stage P.entries) ∧
        (∀ v, (Q.flat v).val 0 ≠ 0) ∧
        (∀ v, (C v).numerator 0 ≠ 0) ∧
        (∀ v, fourier R Q.dq ((C v).numerator 0) 1 ≠ 0) := by
  have hK := PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12
  obtain ⟨f,C,hC⟩ := normalized_tensor_flat_preimage R A D P
  obtain ⟨f',C',hf',hC'⟩ := canonical_flat_residue F R.A.zeta12 R.A.primitive_zeta12 hK f C
  have hf'0 : f'.val 0 = f.val 0 := by ext g; simp [hf']
  have hflat' (s) (g) : f'.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (f'.val 0) g := by
    rw [hf'0,hf']; rfl
  have hext' : ExteriorFixed R (C'.numerator 0) := by
    have he : C'.numerator 0 = tensorFunction R A.factorization D.tensor.stage P.entries :=
      (funext hC').trans hC
    rw [he]
    exact normalized_tensor_exterior R A D P
  obtain ⟨z,Cz,hz,hext,hCz⟩ := exterior_flat_preimage R f' C' hflat' hext'
  have hp : Cz.numerator 0 = tensorFunction R A.factorization D.tensor.stage P.entries :=
    hCz.trans ((funext hC').trans hC)
  letI := A.sources.finite_companions
  let w : R.A.UnitQuotient → Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K := fun _ => z
  obtain ⟨V,hV⟩ := FiniteWhittakerProjectors.canonical_family_level R w (fun _ => hz)
  let Q : AdmissibleFlatSources R := {
    K := (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K
    iwasawa := hK
    flat := w
    finite_companions := A.sources.finite_companions
    level := V
    common_level := hV
    ordinary := fun _ s ε g => ThetaExpansion.induced_ordinary_central_covariance R s _ (z.property.1 s) ε g
    exterior_spherical := ?_
    dq := A.sources.dq
    quotientHaar := A.sources.quotientHaar
    probability := A.sources.probability }
  · refine ⟨Q,rfl,(fun _ => Cz),(fun _ => hp),?_,?_,?_⟩
    · intro v
      exact Cz.zero_section_ne_zero hK (hp ▸ P.realization_nonzero)
    · intro v
      exact hp ▸ P.realization_nonzero
    · intro v
      change fourier R A.sources.dq (Cz.numerator 0) 1 ≠ 0
      rw [hp]
      exact P.period_nonzero
  · intro v s q hq a ha g
    change z.val s (g * finiteInjection R q a) = z.val s g
    rw [hz,hz]
    unfold scalarWeight
    rw [hext q hq a ha]
    have hα := KPContFlatFullProductIwasawa.alpha_mul_compact F R.A.zeta12 R.A.primitive_zeta12 g
      ⟨finiteInjection R q a,finiteInjection_compact_mem R q a ha⟩
    change KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 (g * finiteInjection R q a) =
      KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 g at hα
    rw [hα]

end DedekindZetaZeroFree.RootDerivatives

end
