module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.WeylGeometry
public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.TransportReduction

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct KPLiteralScalarHCCompactOrbit
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

theorem finiteWeyl_factor (v : R.A.UnitQuotient) (z : R.A.G) (q : R.A.Sf) :
    fourier R C.sources.dq (C.realization.theta v) (finiteLift q.val (finiteWeylRaw R z q.val)) /
      fourier R C.sources.dq (C.realization.theta v) 1 =
    ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr q.val) (z.2 q) := by
  unfold ThetaExpansion.normalizedLocalWeylValue KPRationalAdelicSplitting.pglA
  rw [KPRationalAdelicSplitting.A_local,← map_mul,← map_mul]
  congr 1
  congr 1
  congr 1
  unfold finiteWeylRaw
  have h : Units.map (adeleEval F (Sum.inr q.val)).toMonoidHom (localIdele R z) = z.2 q :=
    DigitMasks.localIdele_finite R z q.val q.property
  exact congrArg (fun y => KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) y *
    KPRationalAdelicSplitting.WCoordinates F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)) h

theorem archWeyl_factor (v : R.A.UnitQuotient) (z : R.A.G) (w : InfinitePlace F) :
    archCoefficient (C := C) v w (archWeylMatrix R z w) =
      ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w) (z.1 w) := by
  let y := Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).toMonoidHom (z.1 w)
  have hi : archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
      (Function.update (1 : InfinitePlace F → ComplexGL2) w (KPCplxCharacterHaar.diagonal y * weyl)) =
      archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
        (Function.update 1 w (KPCplxCharacterHaar.diagonal y)) *
      archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 (Function.update 1 w weyl) := by
    rw [← map_mul]
    congr 1
    funext u
    by_cases hu : u = w <;> simp [hu]
  unfold archCoefficient archWeylMatrix
  rw [hi]
  have hd := SheetRescaling.archMatrixInsertion_local_diagonal R w y
  have hw := SheetRescaling.archMatrixInsertion_local_weyl R w
  change archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
    (Function.update (1 : InfinitePlace F → ComplexGL2) w (KPCplxCharacterHaar.diagonal y)) = _ at hd
  change archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
    (Function.update (1 : InfinitePlace F → ComplexGL2) w weyl) = _ at hw
  rw [hd,hw]
  unfold ThetaExpansion.normalizedLocalWeylValue
  congr 3
  apply congrArg (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12)
  apply congrArg (KPRationalAdelicSplitting.localIdele F (Sum.inl w))
  apply Units.ext
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)) (z.1 w : w.Completion)) = _
  exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm_apply_apply _

theorem globalWeyl_product (v : R.A.UnitQuotient) (z : R.A.G) :
    fourier R C.sources.dq (C.realization.theta v)
      (MomentSources.diagonal R z * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) =
    fourier R C.sources.dq (C.realization.theta v) 1 *
      (∏ p : R.A.Sf, ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) (z.2 p)) *
      ∏ w : InfinitePlace F, ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w) (z.1 w) := by
  rw [fourier_right_sWeyl R C.realization v,diagonal_sWeyl_geometry,
    fullMatrix_product v (finiteWeylRaw R z) (archWeylMatrix R z)]
  simp_rw [finiteWeyl_factor R C v z,archWeyl_factor R C v z]

theorem radial_transport :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ v κ (j : ℕ), j ≤ 2 → ∀ u : ℝ, ∀ y : R.A.G1,
      let z := y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u)
      ‖iteratedDeriv j (fun t => ThetaExpansion.radialSheetIntegrand R C v κ t y) u‖ ≤
        D * ((∏ p : R.A.Sf, ‖ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) (z.2 p)‖) *
          ∑ a : InfinitePlace F → Fin 3, ∏ w : InfinitePlace F,
            ‖ThetaExpansion.localWeylArchJet R C v w (a w).val (z.1 w)‖) :=
  same_source_transport_of_weyl_factorization R C (globalWeyl_product R C)

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
