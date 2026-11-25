/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PointDerivedHom.PointDerivedHomModels
import WeilConjectures.SixFunctors.PointDerivedHom.PointSheafHomMaps
import WeilConjectures.Algebra.Homology.Module.ModuleHomSignedEvaluation

/-! # Signed tensor-Hom evaluation at a point

Source: Stacks Project, Tags 0A8X and 08J7.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.PointDerivedHom

variable (k : Type t) [Field k]
  {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)
  (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
  (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
    L.obj M = extensionObject.{t, u} k B α M)
  (adj : L ⊣ sections.{t, u} k B α)
  (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)

end WeilConjectures.PointDerivedHom
