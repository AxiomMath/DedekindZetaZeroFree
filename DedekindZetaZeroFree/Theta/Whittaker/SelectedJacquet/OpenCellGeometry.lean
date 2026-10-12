module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.LiteralArchNorm
public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanTraceCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open NumberField KPLiteralRaw KPCplxCharacterHaar KPCplxPrincipalSeriesCharts TraceHaarTransport
open KPAdelicCoverRestrictedProduct KPLiteralScalarHCCompactOrbit KPLiteralScalarHCSliceCharts
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def openCellFiniteTuple (u : RestrictedCover F ζ hζ) : RestrictedCover F ζ hζ :=
  ⟨fun v => match v with
    | Sum.inl _ => 1
    | Sum.inr q => u (Sum.inr q), by
    filter_upwards [u.property] with v hv
    cases v with
    | inl w => exact Subgroup.one_mem _
    | inr q => exact hv⟩

def openCellFiniteFactor (u : RestrictedCover F ζ hζ) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ :=
  ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ (openCellFiniteTuple F ζ hζ u)), by
    refine ⟨openCellFiniteTuple F ζ hζ u, ?_, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro w
    rfl⟩

def openCellFiniteUpper (b : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ :=
  ⟨KPGlobalTorusFunctionData.N F ζ hζ (0, b), by
    refine ⟨KPGlobalTorusFunctionData.rootTuple F ζ hζ (0, b), ?_, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro w
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) 0 = 1
    exact KPStandardLocalRootLifts.N_zero F ζ hζ (Sum.inl w)⟩

theorem openCell_arch_upper (a : InfiniteAdeleRing F) :
    KPGlobalTorusFunctionData.N F ζ hζ (a, 0) =
      archMatrixInsertion F ζ hζ (fun w => upperUnipotent (archTraceCoordinates F ζ hζ a w)) := by
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ
    (KPGlobalTorusFunctionData.rootTuple F ζ hζ (a, 0))) =
    scalarQuotient F ζ hζ (amalgamation F ζ hζ
      (KPLiteralChamber.sectionTuple F ζ hζ
        (fun w => upperUnipotent (archTraceCoordinates F ζ hζ a w))))
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q =>
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) 0 = 1
    exact KPStandardLocalRootLifts.N_zero F ζ hζ (Sum.inr q)
  | inl w =>
    change KPLocalCover.sectionMap F ζ hζ (Sum.inl w) _ =
      KPLocalCover.sectionMap F ζ hζ (Sum.inl w) _
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.n, upperUnipotent, Matrix.GeneralLinearGroup.map,
        archTraceCoordinates, Equiv.piCongrRight]
    change a w = (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)) (a w))
    exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm_apply_apply _).symm

theorem openCell_weyl :
    KPRationalAdelicSplitting.pglW F ζ hζ =
      (openCellFiniteFactor F ζ hζ (KPRationalAdelicSplitting.WTuple F ζ hζ)).val *
        archMatrixInsertion F ζ hζ (fun _ => weyl) := by
  change scalarQuotient F ζ hζ
    (amalgamation F ζ hζ (KPRationalAdelicSplitting.WTuple F ζ hζ)) = _
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ _) =
    scalarQuotient F ζ hζ (amalgamation F ζ hζ
      (openCellFiniteTuple F ζ hζ (KPRationalAdelicSplitting.WTuple F ζ hζ))) *
    scalarQuotient F ζ hζ (amalgamation F ζ hζ
      (KPLiteralChamber.sectionTuple F ζ hζ (fun _ => weyl)))
  rw [← map_mul, ← map_mul]
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q =>
    change (KPRationalAdelicSplitting.WTuple F ζ hζ) (Sum.inr q) =
      (KPRationalAdelicSplitting.WTuple F ζ hζ) (Sum.inr q) * 1
    exact (mul_one _).symm
  | inl w =>
    change KPLocalCover.sectionMap F ζ hζ (Sum.inl w) _ = 1 *
      KPLocalCover.sectionMap F ζ hζ (Sum.inl w) _
    rw [one_mul]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [KPStandardLocalRootLifts.weylSwap, weyl, Matrix.GeneralLinearGroup.map]

theorem openCell_arch_finite (a : InfiniteAdeleRing F)
    (b : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (g : InfinitePlace F → ComplexGL2) :
    KPRationalAdelicSplitting.pglW F ζ hζ *
      KPGlobalTorusFunctionData.N F ζ hζ (a, b) * archMatrixInsertion F ζ hζ g =
    ((openCellFiniteFactor F ζ hζ (KPRationalAdelicSplitting.WTuple F ζ hζ)) *
      openCellFiniteUpper F ζ hζ b).val * archMatrixInsertion F ζ hζ
        (fun w => weyl * upperUnipotent (archTraceCoordinates F ζ hζ a w) * g w) := by
  have hN : KPGlobalTorusFunctionData.N F ζ hζ (a, b) =
      KPGlobalTorusFunctionData.N F ζ hζ (a, 0) *
        KPGlobalTorusFunctionData.N F ζ hζ (0, b) := by
    rw [← KPGlobalTorusFunctionData.N_add]
    congr 1
    change (a, b) = (a + 0, 0 + b)
    rw [add_zero, zero_add]
  rw [hN, openCell_arch_upper, openCell_weyl]
  have hc := archMatrixInsertion_commutes_finite F ζ hζ
    (fun w => weyl * upperUnipotent (archTraceCoordinates F ζ hζ a w))
    (openCellFiniteUpper F ζ hζ b)
  change (_ * _) * (_ * (openCellFiniteUpper F ζ hζ b).val) * _ = _
  simp only [Subgroup.coe_mul]
  calc
    _ = (openCellFiniteFactor F ζ hζ (KPRationalAdelicSplitting.WTuple F ζ hζ)).val *
        (archMatrixInsertion F ζ hζ (fun w => weyl * upperUnipotent (archTraceCoordinates F ζ hζ a w)) *
          (openCellFiniteUpper F ζ hζ b).val) * archMatrixInsertion F ζ hζ g := by
            rw [show (fun w => weyl * upperUnipotent (archTraceCoordinates F ζ hζ a w)) =
              (fun _ => weyl) * (fun w => upperUnipotent (archTraceCoordinates F ζ hζ a w)) from rfl,
              map_mul]
            group
    _ = _ := by
      rw [hc.eq, show (fun w => weyl * upperUnipotent (archTraceCoordinates F ζ hζ a w) * g w) =
        (fun w => weyl * upperUnipotent (archTraceCoordinates F ζ hζ a w)) * g from rfl, map_mul]
      group

end DedekindZetaZeroFree.SheetRescaling

end
