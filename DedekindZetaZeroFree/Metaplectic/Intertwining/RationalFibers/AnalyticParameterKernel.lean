module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RationalFibers.ReflectedSeparation
public import DedekindZetaZeroFree.Metaplectic.Intertwining.LocalProducts.CompactChangeAnalyticity

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct Topology
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann
open KPRankOneShellRepair KPRankOneShellContinuation
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open KPComplexIntertwinerParameterMajorant KPComplexStandardIntertwinerGerm
open KPCplxPrincipalSeriesCharts

 def complexZeroLinear : CompactPicture →ₗ[ℂ] PrincipalSeries positiveParameter where
  toFun := zeroForward
  map_add' φ ψ := by
    apply Subtype.ext
    funext g
    exact mul_add _ _ _
  map_smul' c φ := by
    apply Subtype.ext
    funext g
    change _ * (c * φ _) = c * (_ * φ _)
    ring

def complexInput : PrincipalSeries positiveParameter →ₗ[ℂ] CompactPicture :=
  (LinearEquiv.ofBijective complexZeroLinear zero_model_identifications.1).symm.toLinearMap

theorem complexInput_zero (f : PrincipalSeries positiveParameter) :
    zeroForward (complexInput f) = f :=
  (LinearEquiv.ofBijective complexZeroLinear zero_model_identifications.1).apply_symm_apply f

theorem complexInput_forward (f : PrincipalSeries positiveParameter) (z : ℂ)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    forwardSection z (complexInput f) g =
      Complex.exp (2*z*(Real.log (rowRatio g) : ℂ)) * f g := by
  have he : forwardSection 0 (complexInput f) g = f g :=
    congrArg (fun v : PrincipalSeries positiveParameter => v g) (complexInput_zero f)
  rw [← he]
  unfold forwardSection
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

def complexParameterOutput (z : ℂ) (g : KPCplxCharacterHaar.ComplexGL2) :
    CompactPicture →ₗ[ℂ] ℂ :=
  if hz : z ∈ KPComplexStandardIntertwinerGerm.halfPlane then
    { toFun φ := (4 * Real.pi : ℝ) * haarIntegral 1 z φ g
      map_add' φ ψ := by
        have he : ∀ h, forwardSection z (φ + ψ) h =
            forwardSection z φ h + forwardSection z ψ h := fun _ => mul_add _ _ _
        unfold haarIntegral
        simp_rw [he]
        rw [integral_add (haarIntegral_integrable 1 z hz φ g)
          (haarIntegral_integrable 1 z hz ψ g)]
        ring
      map_smul' c φ := by
        have he : ∀ h, forwardSection z (c • φ) h = c * forwardSection z φ h := by
          intro h
          change _ * (c * φ _) = c * (_ * φ _)
          ring
        unfold haarIntegral
        simp_rw [he]
        rw [integral_const_mul]
        change _ * (c * _) = c * (_ * _)
        ring }
  else 0

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

def finiteParameterInput (q : KPFinitePlace F) (J : IwasawaData (C.canonical q).borel)
    (z : ℂ) : Plus R N P C (.inr q) →ₗ[ℂ]
      sectionSpace (C.canonical q).borel (C.polarization q) .plus z :=
  (compactTrivialization (C.canonical q).borel (C.polarization q)
    (C.canonical q).iwasawa .plus z).toLinearMap.comp
    ((LocalCompactChange.correctedCompact F R.A.zeta12 R.A.primitive_zeta12 q
      (C.canonical q) (C.canonical q).iwasawa J (C.polarization q) z).comp
      (compactTrivialization (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .plus 0).symm.toLinearMap)

theorem finiteParameterInput_displacement (q : KPFinitePlace F)
    (J : IwasawaData (C.canonical q).borel) (z : ℂ)
    (f : Plus R N P C (.inr q)) (g : ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) :
    (finiteParameterInput R N P C q J z f).val g =
      Complex.exp (z * (Real.log (LocalCompactChange.forwardAbs F R.A.zeta12
        R.A.primitive_zeta12 q (C.canonical q) J g) : ℂ)) • f.val g := by
  change (compactTrivialization (C.canonical q).borel (C.polarization q)
    (C.canonical q).iwasawa .plus z
    (LocalCompactChange.correctedCompact F R.A.zeta12 R.A.primitive_zeta12 q
      (C.canonical q) (C.canonical q).iwasawa J (C.polarization q) z
      ((compactTrivialization (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .plus 0).symm f))).val g = _
  rw [LocalCompactChange.correctedCompact_displacement, LinearEquiv.apply_symm_apply]

def parameterOutput (J : ∀ q, IwasawaData (C.canonical q).borel)
    (p : KPHilbert.Place F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p) (z : ℂ) :
    Plus R N P C p →ₗ[ℂ] Fiber R P C p :=
  match p with
  | .inl w =>
    (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 a.epsilon : ℂ) •
      ((complexParameterOutput z (complexMatrix R w a)).comp
        (complexInput.comp KPLiteralTensor.harmonicPlus.subtype))
  | .inr q =>
    (arithmeticRootScale R (.inr q) : ℂ) •
      { toFun f := ((transportToSections (LocalField F q) (C.canonical q).borel
          (C.polarization q) (C.canonical q).iwasawa .plus z
          (actualCanonicalContinued F q R.A.zeta12 R.A.primitive_zeta12 (C.canonical q)
            (C.polarization q) (integerHaar R N q) (integerHaar_integer R N q) .plus z))
          (finiteParameterInput R N P C q (J q) z f)).val
            (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a)
        map_add' f h := by simp only [map_add]; rfl
        map_smul' c f := by simp only [map_smul]; rfl }

theorem parameterOutput_zero (J : ∀ q, IwasawaData (C.canonical q).borel)
    (p : KPHilbert.Place F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (f : Plus R N P C p) :
    parameterOutput R N P C J p a 0 f =
      localMinusValue R N P C p a (arithmeticQuotient R N P C p f) := by
  cases p with
  | inl w =>
    have h0 : (0 : ℂ) ∈ KPComplexStandardIntertwinerGerm.halfPlane := by
      norm_num [KPComplexStandardIntertwinerGerm.halfPlane]
    have he : forwardSection 0 (complexInput f.val) = f.val.val :=
      congrArg Subtype.val (complexInput_zero f.val)
    simp only [parameterOutput, LinearMap.smul_apply, LinearMap.comp_apply,
      complexParameterOutput, dite_eq_left h0]
    unfold KPComplexStandardIntertwinerGerm.haarIntegral
    change _ * ((4 * Real.pi : ℝ) *
      ∫ x : ℂ, forwardSection 0 (complexInput f.val)
        (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * complexMatrix R w a)
        ∂KPCplxCharacterHaar.characterHaar 1) = _
    rw [he]
    rfl
  | inr q =>
    simp only [parameterOutput, LinearMap.smul_apply, finiteParameterInput,
      LinearMap.comp_apply, LocalCompactChange.correctedCompact_zero]
    change (arithmeticRootScale R (.inr q) : ℂ) •
      ((transportToSections (LocalField F q) (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .plus 0
        (actualCanonicalContinued F q R.A.zeta12 R.A.primitive_zeta12 (C.canonical q)
          (C.polarization q) (integerHaar R N q) (integerHaar_integer R N q) .plus 0))
        ((compactTrivialization (C.canonical q).borel (C.polarization q)
          (C.canonical q).iwasawa .plus 0)
          ((compactTrivialization (C.canonical q).borel (C.polarization q)
            (C.canonical q).iwasawa .plus 0).symm f))).val _ = _
    rw [LinearEquiv.apply_symm_apply]
    unfold transportToSections
    simp only [LinearMap.comp_apply]
    change (arithmeticRootScale R (.inr q) : ℂ) •
      ((compactTrivialization (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .minus (-0)) _).val _ = _
    rw [neg_zero]
    change _ = (arithmeticRootScale R (.inr q) : ℂ) •
      ((actualCanonicalForwardLinear F R.A.zeta12 R.A.primitive_zeta12 q
        (imageData R N P C q).inducing
        (imageData R N P C q).inducing.polarization
        (imageData R N P C q).haar
        (imageData R N P C q).haar_integer f).val
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a))
    rw [forwardIntegralLinear_eq_continuationWitness]
    rfl

theorem parameterOutput_coordinate_analytic
    (J : ∀ q, IwasawaData (C.canonical q).borel) (p : KPHilbert.Place F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (f : Plus R N P C p) (j : InducingCoordinate R P C p) :
    AnalyticOnNhd ℂ (fun z => inducingCoordinates R P C p
      (parameterOutput R N P C J p a z f) j) KPContinuation.spectralDomain := by
  cases p with
  | inl w =>
    intro z hz
    have he : (fun u => inducingCoordinates R P C (.inl w)
        (parameterOutput R N P C J (.inl w) a u f) j) =ᶠ[𝓝 z]
        (fun u => (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
          R.A.primitive_zeta12 a.epsilon : ℂ) * (4 * Real.pi : ℝ) *
          haarIntegral 1 u (complexInput f.val) (complexMatrix R w a)) := by
      filter_upwards [KPContinuation.spectralDomain_isOpen.mem_nhds hz] with u hu
      have hu' : u ∈ KPComplexStandardIntertwinerGerm.halfPlane := by
        simpa only [KPContinuation.spectralDomain, KPComplexStandardIntertwinerGerm.halfPlane,
          neg_div] using hu
      simp only [parameterOutput, LinearMap.smul_apply, LinearMap.comp_apply,
        complexParameterOutput, dite_eq_left hu', inducingCoordinates]
      change _ * ((4 * Real.pi : ℝ) *
        haarIntegral 1 u (complexInput f.val) (complexMatrix R w a)) = _
      ring
    have ha : AnalyticOnNhd ℂ
        (fun u => haarIntegral 1 u (complexInput f.val) (complexMatrix R w a))
        KPContinuation.spectralDomain := by
      simpa only [KPContinuation.spectralDomain, KPComplexStandardIntertwinerGerm.halfPlane,
        neg_div] using (haarIntegral_holomorphic 1 (complexInput f.val) (complexMatrix R w a)).analyticOnNhd
          halfPlane_open_connected.1
    exact ((analyticAt_const.mul analyticAt_const).mul (ha z hz)).congr he.symm
  | inr q =>
    have ha := KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity.CorrectedOutputAnalytic.finite_corrected_full_right_coordinate_analytic
      F R.A.zeta12 R.A.primitive_zeta12 q (C.canonical q) (C.polarization q) (J q)
      (integerHaar R N q) (integerHaar_integer R N q)
      ((compactTrivialization (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .plus 0).symm f)
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a)
      (Function.surjInv (QuotientGroup.mk'_surjective
        ((C.polarization q).L.comap (C.canonical q).heisenberg.π)) j)
    intro z hz
    convert (analyticAt_const (v := (arithmeticRootScale R (.inr q) : ℂ))).mul (ha z hz) using 1
    funext u
    change (arithmeticRootScale R (.inr q) : ℂ) * _ = _
    rfl

def parameterKernel (J : ∀ q, IwasawaData (C.canonical q).borel)
    (p : KPHilbert.Place F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (z : ℂ) (x : RootPoint R p) : Plus R N P C p →ₗ[ℂ] Fiber R P C p :=
  match p with
  | .inl w =>
    { toFun f := (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
        R.A.primitive_zeta12 a.epsilon : ℂ) *
        forwardSection z (complexInput f.val)
          (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * complexMatrix R w a)
      map_add' f h := by
        simp only [Submodule.coe_add, map_add]
        unfold forwardSection
        change _ * (_ * ((complexInput f.val) _ + (complexInput h.val) _)) = _
        ring
      map_smul' c f := by
        simp only [Submodule.coe_smul, map_smul]
        change _ * (_ * (c * (complexInput f.val) _)) = c * (_ * (_ * (complexInput f.val) _))
        ring }
  | .inr q =>
    { toFun f := (finiteParameterInput R N P C q (J q) z f).val
        ((C.canonical q).borel.liftedW⁻¹ * (C.canonical q).borel.upperRoot (Multiplicative.ofAdd x) *
          KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a)
      map_add' f h := by simp only [map_add]; rfl
      map_smul' c f := by simp only [map_smul]; rfl }

theorem parameterKernel_integrable
    (J : ∀ q, IwasawaData (C.canonical q).borel) (p : KPHilbert.Place F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain)
    (f : Plus R N P C p) (j : InducingCoordinate R P C p) :
    Integrable (fun x => inducingCoordinates R P C p
      (parameterKernel R N P C J p a z x f) j) (arithmeticRootMeasure R N p) := by
  cases p with
  | inl w =>
    have hz' : z ∈ KPComplexStandardIntertwinerGerm.halfPlane := by
      simpa only [KPContinuation.spectralDomain, KPComplexStandardIntertwinerGerm.halfPlane,
        neg_div] using hz
    have hi := (haarIntegral_integrable 1 z hz' (complexInput f.val) (complexMatrix R w a)).const_mul
      (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 a.epsilon : ℂ)
    rw [arithmeticRootMeasure_eq R N (imageData R N P C) (.inl w)]
    exact hi.smul_measure ENNReal.ofReal_ne_top
  | inr q =>
    have hz' : convergenceHalfPlane .plus z := by
      simpa [convergenceHalfPlane, KPContinuation.spectralDomain, neg_div] using hz
    have hi := actualCanonicalContinued_integrable F q R.A.zeta12 R.A.primitive_zeta12
      (C.canonical q) (C.polarization q) (integerHaar R N q) (integerHaar_integer R N q)
      .plus z hz' (finiteParameterInput R N P C q (J q) z f)
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a)
      (Function.surjInv (QuotientGroup.mk'_surjective
        ((C.polarization q).L.comap (C.canonical q).heisenberg.π)) j)
    rw [arithmeticRootMeasure_eq R N (imageData R N P C) (.inr q)]
    exact hi.smul_measure ENNReal.ofReal_ne_top

theorem parameterKernel_integral
    (J : ∀ q, IwasawaData (C.canonical q).borel) (p : KPHilbert.Place F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain)
    (f : Plus R N P C p) (j : InducingCoordinate R P C p) :
    (∫ x, inducingCoordinates R P C p (parameterKernel R N P C J p a z x f) j
      ∂arithmeticRootMeasure R N p) =
      inducingCoordinates R P C p (parameterOutput R N P C J p a z f) j := by
  rw [arithmeticRootMeasure_eq R N (imageData R N P C) p, integral_smul_measure,
    ENNReal.toReal_ofReal (arithmeticRootScale_pos R p).le]
  cases p with
  | inl w =>
    have hz' : z ∈ KPComplexStandardIntertwinerGerm.halfPlane := by
      simpa only [KPContinuation.spectralDomain, KPComplexStandardIntertwinerGerm.halfPlane,
        neg_div] using hz
    change (4 * Real.pi : ℝ) • (∫ x : ℂ,
      (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 a.epsilon : ℂ) *
        forwardSection z (complexInput f.val)
          (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * complexMatrix R w a)
          ∂KPCplxCharacterHaar.characterHaar 1) = _
    rw [integral_const_mul]
    simp only [parameterOutput, LinearMap.smul_apply, LinearMap.comp_apply,
      complexParameterOutput, dite_eq_left hz']
    change (4 * Real.pi : ℝ) •
      ((KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 a.epsilon : ℂ) *
        haarIntegral 1 z (complexInput f.val) (complexMatrix R w a)) =
      (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 a.epsilon : ℂ) *
        ((4 * Real.pi : ℝ) * haarIntegral 1 z (complexInput f.val) (complexMatrix R w a))
    simp only [Complex.real_smul]
    ring
  | inr q =>
    let φ := LocalCompactChange.correctedCompact F R.A.zeta12 R.A.primitive_zeta12 q
      (C.canonical q) (C.canonical q).iwasawa (J q) (C.polarization q) z
      ((compactTrivialization (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .plus 0).symm f)
    have hz' : convergenceHalfPlane .plus z := by
      simpa [convergenceHalfPlane, KPContinuation.spectralDomain, neg_div] using hz
    have he := actualCanonicalContinued_chamber F q R.A.zeta12 R.A.primitive_zeta12
      (C.canonical q) (C.polarization q) (integerHaar R N q) (integerHaar_integer R N q)
      .plus z hz' φ
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a)
      (Function.surjInv (QuotientGroup.mk'_surjective
        ((C.polarization q).L.comap (C.canonical q).heisenberg.π)) j)
    change (arithmeticRootScale R (.inr q) : ℂ) *
      standardIntegralCoordinate (LocalField F q) (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa (integerHaar R N q) .plus z φ _ _ = _
    rw [← he]
    rfl

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
