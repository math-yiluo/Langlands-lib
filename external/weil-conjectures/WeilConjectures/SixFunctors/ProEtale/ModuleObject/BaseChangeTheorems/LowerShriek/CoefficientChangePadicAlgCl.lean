/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePadicAlgCl.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePadicAlgCl.UpperStar

/-!
# The extension of scalars `E ⟶ ℚ̄_ℓ` as a coefficient change

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`. This file shows that the
extension of scalars `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`, with the comparisons (Pull), (Shriek) and
(Push) of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility`, is
a coefficient change of the bounded constructible six functors
(`ProEtale.CondensedRing.toPadicAlgClCoefficientChange`). The required compatibilities are
restrictions of those on the ambient derived categories
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate`).

The components of the comparisons (Pull) and (Shriek), which are those of the ambient comparisons,
are computed in `CoefficientChangePadicAlgCl/UpperStar.lean` and
`CoefficientChangePadicAlgCl/OpenImmersion.lean`, which this file collects.
-/
