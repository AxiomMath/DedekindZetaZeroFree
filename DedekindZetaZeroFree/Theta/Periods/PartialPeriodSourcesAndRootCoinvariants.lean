module

public import DedekindZetaZeroFree.Theta.Periods.ScalarQuotientsAndFourierDescent
public import DedekindZetaZeroFree.Theta.Periods.CompactKernelOrbitData
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Borel.TorusRetraction

@[expose] public section

section

noncomputable section

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 4096

set_option synthInstance.maxHeartbeats 1000000

namespace DedekindZetaZeroFree.KPWildActualSectionAction

open KPGlobalResidualConstruction KPWildPartialPeriodFactorization

open KPLocalExceptionalConstruction

open KPKirillovGenuineSectionCharts

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSection → scalarSection

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSectionAdd → scalarSectionAdd

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarTensor → scalarTensor

attribute [local instance] scalarSectionAdd

end DedekindZetaZeroFree.KPWildActualSectionAction

end

end

section

noncomputable section

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPWildActualFullImageAction

open KPGlobalResidualConstruction KPWildPartialPeriodFactorization KPLocalExceptionalConstruction

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSection → scalarSection

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarTensor → scalarTensor

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSectionAdd → scalarSectionAdd

attribute [local instance] scalarSectionAdd

end DedekindZetaZeroFree.KPWildActualFullImageAction

end

end

section

noncomputable section

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPWildActualFullImageAction

open KPGlobalResidualConstruction KPWildPartialPeriodFactorization KPLocalExceptionalConstruction

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSection → scalarSection

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarTensor → scalarTensor

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSectionAdd → scalarSectionAdd

attribute [local instance] scalarSectionAdd

end DedekindZetaZeroFree.KPWildActualFullImageAction

end

end
