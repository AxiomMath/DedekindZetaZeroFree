module

public import DedekindZetaZeroFree.Moments.Probes.TraceHaarCoordinates

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PrincipalProbeConstruction
variable {F : Type} [Field F] [NumberField F]

theorem exists_shared_principal_probe (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (hη : η.IsPrincipal)
    (principalIdele : C.correction.η_id = 1)
    (containsDifferent : PoissonS.ContainsDifferent F A.Sf) :
    ∃ P : NormalizedProbe.PrincipalData A σ η hS,
      P.correction = C.correction ∧
      ArithmeticBinding A σ η hS C P.allowed P.coefficients ∧
      ∃ N : NormalizedProbe.MellinNormalizationData A σ η hS P,
        ∃ R : PoissonNormalizedRow.Normalization A σ η hS P,
          R.localMeasure = N.finiteMeasure := by
  obtain ⟨G, D, B⟩ := exists_arithmetic_binding A σ η hS C hη principalIdele
  obtain ⟨Q, ν, hν, hdis⟩ := exists_domain_with_disintegration A σ η hS C
  obtain ⟨U, ⟨frequencies⟩⟩ := exists_frequency_representatives A σ η hS C G B.sameComplement
  obtain ⟨μ, hμ, hlocal, hprod⟩ := exists_trace_normalized_haar A
  obtain ⟨hcontinuous, htrace, hconductor⟩ := canonical_trace_contract A hS
  obtain ⟨W1, W0, hannular, hcompact, hunits, hnonzero, hzero, hmellin, hW1⟩ :=
    probe_fixed_weight_construction F A (fun v => ResidueTrace.localTraceCharacter v.val)
      hcontinuous htrace (NormalizedProbe.poissonAdditiveMeasure A μ) ν hprod hν
  let P : NormalizedProbe.PrincipalData A σ η hS := {
    principal := hη
    correction := C.correction
    principalIdele := principalIdele
    coefficients := D
    allowed := G
    sameComplement := B.sameComplement
    sameGenerator := B.sameGenerator
    exteriorCharacters := B.exteriorCharacters
    theta_principal := B.theta
    gammaTwo_recipe := B.gammaTwo
    sixthUnitCharacters := B.sixthUnits
    unitReps := U
    frequencies := frequencies
    domain := Q
    finiteTrace := fun v => ResidueTrace.localTraceCharacter v.val
    continuousTrace := hcontinuous
    traceCompatible := htrace
    sameTrace := B.sameTrace
    additiveMeasure := NormalizedProbe.poissonAdditiveMeasure A μ
    additiveHaar := hprod
    multiplicativeMeasure := ν
    multiplicativeHaar := hν
    W0 := W0
    W1 := W1
    annular := hannular
    compactSupport := hcompact
    supportUnits := hunits
    nonzero := hnonzero
    zeroFrequency := hzero
    nonzeroMellin := hmellin }
  refine ⟨P, rfl, B, ?_⟩
  refine ⟨{
    finiteMeasure := μ
    finiteHaar := hμ
    localNormalization := hlocal
    containsDifferent := containsDifferent
    sameAdditiveMeasure := rfl
    sameFiniteTrace := fun _ => rfl
    disintegration := hdis }, ?_⟩
  refine ⟨{
    localMeasure := μ
    localHaar := hμ
    localNormalization := hlocal
    traceConductor := hconductor
    containsDifferent := containsDifferent
    sameMeasure := poisson_measure_coordinate_coherence A μ }, rfl⟩

end DedekindZetaZeroFree.PrincipalProbeConstruction

end
