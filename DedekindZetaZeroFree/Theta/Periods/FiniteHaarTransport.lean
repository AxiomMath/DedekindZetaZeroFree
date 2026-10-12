module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
open scoped NumberField Classical ENNReal
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}

theorem integer_eq_normBall (q : KPFinitePlace F) :
    ((valuation (q.adicCompletion F)).integer : Set (q.adicCompletion F)) =
      {x | ‖x‖ ≤ 1} := by
  ext x
  change valuation (q.adicCompletion F) x ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← map_one (valuation (q.adicCompletion F)), ← Valuation.Compatible.vle_iff_le]
  change Valued.v x ≤ Valued.v 1 ↔ ‖x‖ ≤ 1
  simpa only [norm_one] using (Valued.toNormedField.norm_le_iff (x := x) (x' := 1)).symm

theorem finiteHaar_transport (N : MomentSources.TraceHaarTransport R)
    (q : KPFinitePlace F) (M : MomentSources.LocalImageData R q) :
    N.finiteHaar q = ENNReal.ofReal (PoissonS.integerVolume F q) • M.haar := by
  letI := N.finiteHaar_add q
  have h := Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen (N.finiteHaar q) M.haar
    (valuation (q.adicCompletion F)).isOpen_integer
  rw [M.haar_integer, integer_eq_normBall q, N.finite_mass q] at h
  have hc : (N.finiteHaar q).addHaarScalarFactor M.haar =
      ENNReal.ofReal (PoissonS.integerVolume F q) := by
    simpa only [ENNReal.smul_def, smul_eq_mul, mul_one] using h.symm
  rw [Measure.isAddLeftInvariant_eq_smul (N.finiteHaar q) M.haar,
    ← Measure.coe_nnreal_smul, hc]

def jointHaarFactorizedSources_of_factorization {N : MomentSources.TraceHaarTransport R} (C : MomentSources.JointRealizedFlatSources R N)
    (D : MomentSources.SourceFactorization R C.sources C.realization) : MomentSources.JointHaarFactorizedSources R N where
  toJointRealizedFlatSources := C
  factorization := D
  localHaarTransport := fun q => finiteHaar_transport C.transport q (D.finiteData q)

end DedekindZetaZeroFree.FourierContinuation

end
