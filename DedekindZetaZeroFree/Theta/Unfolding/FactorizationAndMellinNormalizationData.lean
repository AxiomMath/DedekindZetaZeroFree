module

public import DedekindZetaZeroFree.Theta.Whittaker.LocalImageFactors
public import DedekindZetaZeroFree.Theta.Periods.ResidualLieWordSpan
public import DedekindZetaZeroFree.Theta.Profiles.LocalTensorActions
public import DedekindZetaZeroFree.CharacterSums.Gauss.SignedUniformizerTransport
public import DedekindZetaZeroFree.Moments.Probes.AbsoluteSeriesRowDecay
public import DedekindZetaZeroFree.Moments.Probes.ForwardSeriesUniformMajorant
public import DedekindZetaZeroFree.Theta.Unfolding.SheetFundamentalDomains
public import DedekindZetaZeroFree.Theta.Digits.ResidueAverages
public import DedekindZetaZeroFree.Adeles.Haar.PolarProduct
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions
public import DedekindZetaZeroFree.Moments.Reflected.FiniteProfileLogBounds

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.MomentSources
open scoped NumberField Classical Topology ENNReal
open NumberField MeasureTheory ValuativeRel
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

structure TraceHaarTransport where
  signedUniformizer : SignedUniformizerTransport R
  finiteHaar : ∀ p : KPFinitePlace F, Measure (p.adicCompletion F)
  finiteHaar_add : ∀ p, (finiteHaar p).IsAddHaarMeasure
  finite_mass : ∀ p, finiteHaar p {x | ‖x‖ ≤ 1} = ENNReal.ofReal (PoissonS.integerVolume F p)
  complexHaar : Measure ℂ
  complex_mass : complexHaar = (2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea
  finiteMultHaar : ∀ p : R.A.Sf, Measure (p.val.adicCompletion F)ˣ
  finiteMultHaar_isHaar : ∀ p, (finiteMultHaar p).IsHaarMeasure
  angularHaar : InfinitePlace F → Measure Circle
  angularHaar_isHaar : ∀ w, (angularHaar w).IsHaarMeasure
  groupHaar : Measure R.A.G
  groupHaar_isHaar : groupHaar.IsHaarMeasure
  polar_transport : groupHaar = ThetaPositiveSheetMellin.productHaar R.A finiteMultHaar angularHaar
  disintegration : ∀ v₀ : InfinitePlace F, letI := groupHaar_isHaar;
    letI : MeasurableSpace R.A.G1 := borel _;
    letI : MeasurableSpace R.A.G := borel _;
    Measure.map (ThetaProfileHaarSheets.normSplit R.A v₀)
      (ThetaProfileHaarSheets.positiveHaar.prod R.probe.domain.measure) = groupHaar
  section_independent : ∀ (x : ThetaProfileHaarSheets.PositiveAxis) (z : R.A.G1) (f : R.A.G → ℂ),
    letI : MeasurableSpace R.A.G1 := borel _;
    Integrable (fun y : R.A.G1 => f (y.val * R.A.radialSection x.val x.property)) R.probe.domain.measure →
    (MeasureTheory.integral R.probe.domain.measure (fun y : R.A.G1 =>
      f (y.val * z.val * R.A.radialSection x.val x.property))) =
    MeasureTheory.integral R.probe.domain.measure (fun y : R.A.G1 => f (y.val * R.A.radialSection x.val x.property))

structure SourceFactorization (Q : AdmissibleFlatSources R) (T : Realization R Q) where
  finiteData : ∀ q, LocalImageData R q
  references : ∀ p, actualLocal R finiteData p
  bad : Finset (KPHilbert.Place F)
  bad_exact : ∀ p, p ∈ bad ↔ (∃ w : InfinitePlace F, p = Sum.inl w) ∨
    (∃ q : KPFinitePlace F, p = Sum.inr q ∧ q ∈ R.A.Sf)
  ell : ∀ p, actualLocal R finiteData p →ₗ[ℂ] ℂ
  reference_value : ∀ p ∉ bad, ell p (references p) = 1
  scalarSlot : R.A.Sf
  coreMap : RestrictedTensorSimple.Core (actualLocal R finiteData) references bad →ₗ[ℂ] Functions R
  selected : R.A.UnitQuotient → RestrictedTensorSimple.Core (actualLocal R finiteData) references bad
  selected_eq : ∀ v, coreMap (selected v) = T.theta v

  selected_frozen_stage : ∀ v, ∃ (s : RestrictedTensorSimple.Level bad)
    (x : ∀ p : s.val, actualLocal R finiteData p), s.val = bad ∧
      selected v = RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x)
  core_injective : Function.Injective coreMap
  core_same_residue : ∀ x, coreMap x ∈ sameResidueModule T
  finite_intertwining : ∀ q (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (s : RestrictedTensorSimple.Level bad) (hq : Sum.inr q ∈ s.val)
    (x : ∀ p : s.val, actualLocal R finiteData p) g,
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          q (finiteData q).inducing (finiteData q).inducing.polarization
          (finiteData q).haar (finiteData q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩))))) g =
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x))
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a))

  complex_intertwining : ∀ (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (s : RestrictedTensorSimple.Level bad) (hw : Sum.inl w ∈ s.val)
    (x : ∀ p : s.val, actualLocal R finiteData p) g,
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w, hw⟩
        (KPGlobalResidualConstruction.complexCoreSU2Action k (x ⟨Sum.inl w, hw⟩))))) g =
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x))
      (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k)
  product_integrable : ∀ (s : RestrictedTensorSimple.Level bad) (x : ∀ p : s.val, actualLocal R finiteData p),
    Integrable (fun q => coreMap (RestrictedTensorSimple.stageInclusion _ references bad s
      (PiTensorProduct.tprod ℂ x))
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q)) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq
  product_exact : ∀ (s : RestrictedTensorSimple.Level bad) (x : ∀ p : s.val, actualLocal R finiteData p),
    fourier R Q.dq (coreMap (RestrictedTensorSimple.stageInclusion _ references bad s
      (PiTensorProduct.tprod ℂ x))) 1 = ∏ p : s.val, ell p (x p)
  spherical_reference : ∀ (q : KPFinitePlace F), q ∉ R.A.Sf →
    references (Sum.inr q) ≠ 0 ∧ ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q),
      k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) →
      KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q (finiteData q).inducing (finiteData q).inducing.polarization (finiteData q).haar (finiteData q).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) k)
        (references (Sum.inr q)) = references (Sum.inr q)
  detected_tensor : ∃ (s : RestrictedTensorSimple.Level bad) (x : ∀ p : s.val, actualLocal R finiteData p),
    s.val = bad ∧ fourier R Q.dq (coreMap (RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x))) 1 ≠ 0
  period_integrable : ∀ v g, Integrable (fun q => T.theta v
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
      star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq
  detected : ∃ v, fourier R Q.dq (T.theta v) 1 ≠ 0

def SourceFactorization.exteriorValue {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) : ℂ :=
  D.ell (Sum.inr p.val)
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12 p.val
      (D.finiteData p.val).inducing (D.finiteData p.val).inducing.polarization
      (D.finiteData p.val).haar (D.finiteData p.val).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (KPRationalAdelicSplitting.ACoordinates F R.A.zeta12 R.A.primitive_zeta12
          (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
            (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)) (Sum.inr p.val)))
      (D.references (Sum.inr p.val)))

structure ExteriorCoefficients (Q : AdmissibleFlatSources R) (T : Realization R Q)
    (D : SourceFactorization R Q T) : Prop where
  rational_exact : ∀ p x, D.exteriorValue R p x =
    ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p x
  crt_product : ∀ (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior)
    (P : Finset (ThetaBranch.ExteriorPrime R.A)),
    c.val.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal c.val.val →
    n.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal n.val →
    let b := ∏ p ∈ P, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) ^
      (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val)
    (∏ p ∈ P, D.exteriorValue R p b) = R.probe.coefficients.gammaTwo c /
      ((Real.sqrt (R.A.exteriorNorm c.val) : ℂ) * (R.A.exteriorNorm n : ℂ))
  local_exact : ∀ (p : ThetaBranch.ExteriorPrime R.A) (e : ℤ)
    (u : (p.val.adicCompletion F)ˣ) (t : 𝓞 F),
    ‖(u : p.val.adicCompletion F) - algebraMap (𝓞 F) (p.val.adicCompletion F) t‖ < 1 →
    valuation (p.val.adicCompletion F) (u : p.val.adicCompletion F) = 1 →
    D.ell (Sum.inr p.val)
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12 p.val
        (D.finiteData p.val).inducing (D.finiteData p.val).inducing.polarization
        (D.finiteData p.val).haar (D.finiteData p.val).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (KPRationalAdelicSplitting.ACoordinates F R.A.zeta12 R.A.primitive_zeta12
            (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
              ((Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom
                (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p))) ^ e * u)) (Sum.inr p.val)))
        (D.references (Sum.inr p.val))) =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p) e *
        ThetaBranch.residueCharacter R.A R.σ p (Ideal.Quotient.mk p.val.asIdeal t) ^ (2 * e)

def ForwardIdentity (Q : AdmissibleFlatSources R) (T : Realization R Q) (P : Packet R Q) : Prop :=
  ∀ v y, fourier R Q.dq (T.theta v) (diagonal R y) = P.forwardProfile v y

structure ResidualConstantTerm (Q : AdmissibleFlatSources R) (T : Realization R Q) : Prop where
  integrable : ∀ v g, Integrable (fun q => T.theta v
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) Q.dq
  radial : ∀ v (w : InfinitePlace F) (z : w.Completionˣ) (g : Group R),
    upper R Q.dq (T.theta v)
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) * g) =
      (Real.rpow (‖(z : w.Completion)‖ ^ 2) (1 / 3) : ℂ) * upper R Q.dq (T.theta v) g

structure MellinGaussian (N : TraceHaarTransport R) (Q : AdmissibleFlatSources R) (P : Packet R Q) : Prop where

  C₀_exact : P.C₀ =
    (∏ p : R.A.Sf, (N.finiteMultHaar p (P.cutoff p : Set (p.val.adicCompletion F)ˣ)).toReal) *
    (∏ w : InfinitePlace F, (N.angularHaar w Set.univ).toReal) *
    ∏ w : InfinitePlace F, (2 / P.scale w ^ 2)
  positive_sheet_integrable : ∀ x : ThetaProfileHaarSheets.PositiveAxis,
    letI : MeasurableSpace R.A.G1 := borel _;
    Integrable (fun z : R.A.G1 =>
      let y := z.val * R.A.radialSection x.val x.property
      (if ∀ p : R.A.Sf, y.2 p ∈ P.cutoff p then 1 else 0) *
        ∏ w : InfinitePlace F, ‖(y.1 w : w.Completion)‖ ^ 2 *
          KThird (P.scale w * Real.sqrt (‖(y.1 w : w.Completion)‖ ^ 2))) R.probe.domain.measure
  C₀_pos : 0 < P.C₀
  mellin_integrable : ∀ s : ℂ, -(5 / 6 : ℝ) < s.re → Integrable
    (fun x : ThetaProfileHaarSheets.PositiveAxis => (P.positiveSheet x : ℂ) * (x.val : ℂ) ^ s)
    ThetaProfileHaarSheets.positiveHaar
  mellin : ∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
    (∫ x : ThetaProfileHaarSheets.PositiveAxis, (P.positiveSheet x : ℂ) * (x.val : ℂ) ^ s
      ∂ThetaProfileHaarSheets.positiveHaar) = (P.C₀ : ℂ) * (P.A₀ : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ Fintype.card (InfinitePlace F)
  smoothing_integrable : ∀ x : ThetaProfileHaarSheets.PositiveAxis, Integrable
    (fun t : ThetaProfileHaarSheets.PositiveAxis => P.kernel t.val *
      (P.positiveSheet ⟨x.val * t.val, mul_pos x.property t.property⟩ : ℂ)) ThetaProfileHaarSheets.positiveHaar
  smoothing : ∀ x : ThetaProfileHaarSheets.PositiveAxis,
    (∫ t : ThetaProfileHaarSheets.PositiveAxis, P.kernel t.val *
      (P.positiveSheet ⟨x.val * t.val, mul_pos x.property t.property⟩ : ℂ)
      ∂ThetaProfileHaarSheets.positiveHaar) = (thetaReflectionGaussian x.val : ℂ)
end DedekindZetaZeroFree.MomentSources

end
