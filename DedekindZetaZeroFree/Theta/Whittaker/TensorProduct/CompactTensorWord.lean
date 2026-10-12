module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.SlotWord
public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.FinitePeriod
public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.CompactPeriod

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {N : TraceHaarTransport R} {C : JointDigitDescentSources R N}

def mixedRaw (k : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (p : KPHilbert.Place F) : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p :=
  match p with
  | Sum.inl w => KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
      (Matrix.GeneralLinearGroup.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm.toRingHom
        (KPCplxCharacterHaar.complexSU2Embedding (k w)))
  | Sum.inr q => a q

def mixedAction (k : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (p : KPHilbert.Place F) : actualLocal R C.factorization.finiteData p →
      actualLocal R C.factorization.finiteData p :=
  match p with
  | Sum.inl w => KPGlobalResidualConstruction.complexCoreSU2Action (k w)
  | Sum.inr q => KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      q (C.factorization.finiteData q).inducing (C.factorization.finiteData q).inducing.polarization
      (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (a q))

theorem mixed_intertwining (k : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (s : RestrictedTensorSimple.Level C.factorization.bad) (p : s.val)
    (x : ∀ p : s.val, actualLocal R C.factorization.finiteData p) (g : Group R) :
    C.factorization.coreMap (RestrictedTensorSimple.stageInclusion _ C.factorization.references
      C.factorization.bad s (PiTensorProduct.tprod ℂ
        (Function.update x p (mixedAction (C := C) k a p.val (x p))))) g =
    C.factorization.coreMap (RestrictedTensorSimple.stageInclusion _ C.factorization.references
      C.factorization.bad s (PiTensorProduct.tprod ℂ x))
      (g * scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val))) := by
  rcases p with ⟨p,hp⟩
  cases p with
  | inl w => exact C.factorization.complex_intertwining w (k w) s hp x g
  | inr q => exact C.factorization.finite_intertwining q (a q) s hp x g

theorem FrozenTensor.mixed_word_exact {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (k : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    fourier R C.sources.dq (C.realization.theta v)
      ((Finset.univ.toList.map (fun p : X.level.val =>
        scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val)))).prod) =
      ∏ p : X.level.val, C.factorization.ell p (mixedAction (C := C) k a p.val (X.component p)) := by
  let T := fun x => C.factorization.coreMap (RestrictedTensorSimple.stageInclusion _
    C.factorization.references C.factorization.bad X.level (PiTensorProduct.tprod ℂ x))
  let L := fun p : X.level.val => mixedAction (C := C) k a p.val
  let A := fun p : X.level.val => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val))
  have ht (g : Group R) := independent_slot_word T L A
    (mixed_intertwining k a X.level) Finset.univ.toList.reverse
      (List.nodup_reverse.mpr (Finset.nodup_toList _)) X.component g
  simp only [List.mem_reverse,Finset.mem_toList,Finset.mem_univ,ite_true,List.reverse_reverse] at ht
  have hf : T (fun p => L p (X.component p)) =
      fun g => C.realization.theta v (g * (Finset.univ.toList.map A).prod) := by
    funext g
    rw [ht]
    exact congrFun X.function_eq _
  have hi := C.factorization.product_integrable X.level (fun p => L p (X.component p))
  rw [← C.factorization.product_exact X.level (fun p => L p (X.component p))]
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards with q
  rw [show C.factorization.coreMap (RestrictedTensorSimple.stageInclusion _
    C.factorization.references C.factorization.bad X.level
      (PiTensorProduct.tprod ℂ (fun p => L p (X.component p)))) = T (fun p => L p (X.component p)) from rfl,
    hf,mul_one]

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
