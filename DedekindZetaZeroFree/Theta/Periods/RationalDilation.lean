module

public import DedekindZetaZeroFree.Theta.Unfolding.AdditiveFourierExtraction
public import DedekindZetaZeroFree.Adeles.Quotients.RationalDilation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma rationalLift_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 (Matrix.ProjGenLinGroup.mk m) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.rationalHom F R.A.zeta12 R.A.primitive_zeta12 m) := by
  let n := Quotient.out (Matrix.ProjGenLinGroup.mk m)
  have hn : Matrix.ProjGenLinGroup.mk n = Matrix.ProjGenLinGroup.mk m := Quotient.out_eq' _
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hn
  let φ := (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (KPAdelicCoverRestrictedProduct.rationalHom F R.A.zeta12 R.A.primitive_zeta12)
  have hs : φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = 1 :=
    KPRationalAdelicSplitting.rationalScalars_le_ker F R.A.zeta12 R.A.primitive_zeta12 ⟨z, rfl⟩
  change φ n = φ m
  rw [← hz, map_mul, hs, mul_one]

lemma theta_rational_root {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (a : F) (g : Group R) :
    T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) a) * g) = T.theta v g := by
  have h := (T.automorphic v).2.1 (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n F a)) g
  rw [rationalLift_mk] at h
  change T.theta v (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (KPRationalAdelicSplitting.N F R.A.zeta12 R.A.primitive_zeta12 _) * g) = _
  rw [KPRationalAdelicSplitting.N_rational]
  exact h

lemma theta_rational_diagonal {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) :
    T.theta v (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) * g) = T.theta v g := by
  have h := (T.automorphic v).2.1 (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d F a 1)) g
  rw [rationalLift_mk] at h
  have he := KPRationalAdelicSplitting.A_rational F R.A.zeta12 R.A.primitive_zeta12 a
  exact (congrArg (fun b => T.theta v
    (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 b * g)) he).trans h

lemma theta_root_representative {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) (x y : KPAdeles F)
    (hxy : (QuotientAddGroup.mk x : KPAdditiveQuotient F) = QuotientAddGroup.mk y) :
    T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) =
      T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 y * g) := by
  have hmem := QuotientAddGroup.eq.mp hxy
  obtain ⟨a, ha⟩ := hmem
  have hx : x = algebraMap F (KPAdeles F) (-a) + y := by
    change algebraMap F (KPAdeles F) a = -x + y at ha
    rw [map_neg]
    linear_combination ha
  rw [hx, KPGlobalTorusFunctionData.N_add, mul_assoc, theta_rational_root]

lemma fourier_integrand_mk {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) (x : KPAdeles F) :
    T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out (QuotientAddGroup.mk x : KPAdditiveQuotient F)) * g) *
        star (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ) =
    T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) *
      star (adelicTraceCharacter F x : ℂ) := by
  rw [theta_root_representative R T v g _ x (Quotient.out_eq _)]
  exact congrArg (fun c : Circle => T.theta v
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) * star (c : ℂ))
      (adelicTraceQuotientCharacter_mk F x)

def rationalFrequencyValue {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) : ℂ :=
  ∫ q : KPAdditiveQuotient F,
    T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
      star (adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * Quotient.out q) : ℂ) ∂Q.dq

theorem rationalFrequencyValue_integrable_eq {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => C.realization.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * Quotient.out q) : ℂ)) C.sources.dq ∧
    rationalFrequencyValue R C.realization v a g =
      fourier R C.sources.dq (C.realization.theta v)
        (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
          (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) * g) := by
  let D := KPAdditiveRationalDilation.quotientDilation F a
  let A := KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  let f : KPAdditiveQuotient F → ℂ := fun q => C.realization.theta v
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * (A * g)) *
      star (adelicTraceQuotientCharacter F q : ℂ)
  letI := C.sources.quotientHaar
  letI : IsProbabilityMeasure C.sources.dq := ⟨C.sources.probability⟩
  have hmp := KPAdditiveRationalDilation.quotientDilation_measurePreserving F a C.sources.dq
  obtain ⟨e, he⟩ := KPAdditiveRationalDilation.quotientDilation_is_additive_homeomorphism F a
  have hme : MeasurableEmbedding D := by
    have hef : (e : _ → _) = D := funext he
    rw [← hef]
    exact e.toHomeomorph.measurableEmbedding
  have hint : Integrable f C.sources.dq := C.factorization.period_integrable v (A * g)
  have htransform (q : KPAdditiveQuotient F) : f (D q) =
      C.realization.theta v
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * Quotient.out q) : ℂ) := by
    let x := Quotient.out q
    have hq : (QuotientAddGroup.mk x : KPAdditiveQuotient F) = q := Quotient.out_eq q
    have hd : D q = QuotientAddGroup.mk (algebraMap F (KPAdeles F) (a : F) * x) := by
      rw [← hq]; rfl
    change C.realization.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out (D q)) * (A * g)) *
        star (adelicTraceQuotientCharacter F (D q) : ℂ) = _
    rw [hd, fourier_integrand_mk]
    congr 1
    rw [← mul_assoc]
    have hc := KPRationalAdelicSplitting.quotient_upper_diagonal F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) (a : F) * x)
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
    change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) (a : F) * x) * A = A *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          ((algebraMap F (KPAdeles F) (a : F) * x) * algebraMap F (KPAdeles F) (a⁻¹ : Fˣ)) at hc
    have hx : (algebraMap F (KPAdeles F) (a : F) * x) *
        algebraMap F (KPAdeles F) (a⁻¹ : Fˣ) = x := by
      rw [mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
    rw [hx] at hc
    rw [hc, mul_assoc, theta_rational_diagonal]
  have h := hmp.integral_comp hme f
  change (∫ q, f (D q) ∂C.sources.dq) = _ at h
  simp_rw [htransform] at h
  refine ⟨?_, h⟩
  have hi := (hmp.integrable_comp_emb hme).mpr hint
  change Integrable (fun q => f (D q)) C.sources.dq at hi
  simpa only [htransform] using hi

theorem rationalFrequencyValue_eq {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) :
    rationalFrequencyValue R C.realization v a g =
      fourier R C.sources.dq (C.realization.theta v)
        (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
          (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) * g) :=
  (rationalFrequencyValue_integrable_eq R C v a g).2

lemma orbitFrequencyValue_eq_fourier {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (i : ThetaExpansion.SignedExpansion.OrbitIndex R) (g : Group R) :
    orbitFrequencyValue R C.sources C.realization v i g =
      fourier R C.sources.dq (C.realization.theta v)
        (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
          (Units.map (algebraMap F (KPAdeles F)).toMonoidHom ((Quotient.out i.1) * i.2.val)) * g) :=
  rationalFrequencyValue_eq R C v _ g

end DedekindZetaZeroFree.OrbitExpansion

end
