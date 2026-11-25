/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom
import all WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import all WeilConjectures.WeilSheaf.DerivedHom
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.Algebra.Homology.BifunctorHomCone
import all WeilConjectures.Algebra.Homology.BifunctorHomComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra

/-! # Flatness under ordinary geometric open restriction
Source: Stacks 05VD and 0E8I.
(blueprint: lem-sf-native-adic-restriction-flat).
-/

@[expose] public section
set_option autoImplicit false
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (l : ℕ) [Fact l.Prime] {U Z : Scheme.{u}}
  (j : U ⟶ Z) [IsOpenImmersion j]

/-- Ordinary inverse image along the geometric open preserves flat module objects.
Source: Stacks 05VD, inverse image of flat modules, and 0E8I, localization of sites.
(blueprint: lem-sf-native-adic-restriction-flat).

Proof: extension by zero is exact and fully faithful. The open-restriction
internal-Hom comparison and uniqueness of left adjoints give the projection
formula identifying extension by zero after tensoring with the restriction of M
with tensoring by M after extension by zero. For flat M the latter composite is
exact. Exactness of tensoring by its restriction follows by reflection through
the fully faithful extension-by-zero functor. Symmetry gives exactness in the
other variable. This argument also applies to the empty open and zero modules. -/
theorem native_adic_restriction_flat :
    (ProEtale.adicUpperStar l j).PreservesFlat := by
  let f := j
  let R := ProEtale.adicUpperStar l f
  let E := ProEtale.adicOpenImmersionLowerShriek l f
  let adj := ProEtale.adicOpenImmersionLowerShriekAdjunction l f
  let ff : E.FullyFaithful := adj.fullyFaithfulLOfIsIsoUnit
  let : E.Full := ff.full
  let : E.Faithful := ff.faithful
  constructor
  intro M hM
  have e : E ⋙ MonoidalCategory.tensorRight M ≅
      MonoidalCategory.tensorRight (R.obj M) ⋙ E :=
    Functor.isoWhiskerLeft E (PrecompositionAux.tensorIso M).symm ≪≫
      ((adj.comp (Mod.ihomAdjunction M)).ofNatIsoRight
        (ProEtale.adicUpperStarIhomIso l f M)).leftAdjointUniq
          ((Mod.ihomAdjunction (R.obj M)).comp adj) ≪≫
      Functor.isoWhiskerRight (PrecompositionAux.tensorIso (R.obj M)) E
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight M) := hM.2.1
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight M) := hM.2.2
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight (R.obj M) ⋙ E) :=
    preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight (R.obj M) ⋙ E) :=
    preservesFiniteColimits_of_natIso e
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight (R.obj M)) :=
    preservesFiniteLimits_of_reflects_of_preserves _ E
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight (R.obj M)) :=
    preservesFiniteColimits_of_reflects_of_preserves _ E
  exact ⟨⟨preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight (R.obj M)).symm,
    preservesFiniteColimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight (R.obj M)).symm⟩,
    (inferInstance : PreservesFiniteLimits _),
    (inferInstance : PreservesFiniteColimits _)⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
