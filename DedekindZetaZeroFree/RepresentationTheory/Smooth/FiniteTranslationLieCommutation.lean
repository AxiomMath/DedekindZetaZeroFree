module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.CasimirParameterJets

@[expose] public section

noncomputable section
open scoped NumberField Classical
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualScalarCasimirTransport
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem insertion_commutes_finitePart
    (r : KPSmoothActualFlowData.GInfinity F)
    (a : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ r) a.val := by
  have ht : a.val ∈ ActualFiniteFactor.tupleFactor F ζ hζ := by
    obtain ⟨b, hb, he⟩ := a.property
    refine ⟨b, ?_, he⟩
    intro w
    exact (Subgroup.mem_iInf.mp hb) w
  have ha : a.val ∈ ActualFiniteFactor.finiteSubgroup F ζ hζ := by
    rw [ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
    exact ht
  exact ActualFiniteFactor.archInsertion_commutes F ζ hζ r ⟨a.val, ha⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualScalarCasimirTransport

end

section

noncomputable section
open scoped NumberField Classical
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualScalarCasimirTransport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

theorem insertion_commutes_finiteRepresentative
    (r : KPSmoothActualFlowData.GInfinity F)
    (a : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ r) a.val := by
  have ha : a.val ∈ ActualFiniteFactor.finiteSubgroup F ζ hζ := by
    rw [ActualFiniteFactor.finiteSubgroup_eq_ker]
    change ActualFiniteFactor.archProjection F ζ hζ a.val = 1
    funext w
    rw [KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.archProjection_compare]
    have hp := congrFun (show KPCuspGenuineMonodromy.archProjection F ζ hζ a.val = 1 from a.property) w
    rw [hp]
    exact map_one _
  exact ActualFiniteFactor.archInsertion_commutes F ζ hζ r ⟨a.val, ha⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualScalarCasimirTransport

end
end
