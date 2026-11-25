/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleHomPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleHomSingle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitBallRingObj.UnitBallLisseHypotheses

/-!

# The six functors on bounded constructible module objects over `T̲` and `𝒪̲_E = O̲`

`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` restricts the
pushforward, the lower shriek, the derived tensor product and the derived hom to the bounded
constructible derived categories `Dᵇc(X)⟦Λ⟧` separately for each of the three `ℓ`-adic coefficient
rings `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E` (`E ⊆ ℚ̄_ℓ`). This file does the same, with the same declaration
names and statements, for two further coefficient rings of Deligne's finiteness theorems:

* `T̲ = Profinite.continuousMapRingObj T` for a finite discrete ring `T` in which `ℓ` is
  nilpotent (`[Fact (IsNilpotent (ℓ : T))]`), in the namespace
  `ProEtale.CondensedRing.FiniteDiscreteRingObj`
  (`FiniteDiscreteRingObj.boundedConstructibleLowerStar ℓ T f`);
* `O̲ = Profinite.continuousMapRingObj O` for the closed unit ball `O` of a finite normed
  extension `E` of `ℚ_ℓ` (`O : Subring E` with `[Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]`), in the
  namespace `ProEtale.CondensedRing.UnitBallRingObj`
  (`UnitBallRingObj.boundedConstructibleLowerStar ℓ O f`).

The setting is the one of `BoundedConstructible`: `ℓ` is a prime and `k` a field of characteristic
`p > 0` with `p ≠ ℓ`, all schemes are objects `X : Over (Spec (.of k))` separated and of finite
type over `Spec k`, and all morphisms are morphisms of `Over (Spec (.of k))`. The pullback
`boundedConstructibleUpperStar` and the extension by zero
`boundedConstructibleOpenImmersionLowerShriek` are stated there for a general `Λ`.

| functor | `FiniteDiscreteRingObj` (`T̲`) | `UnitBallRingObj` (`O̲`) |
| --- | --- | --- |
| `Rf_*` | `boundedConstructibleLowerStar` | `boundedConstructibleLowerStar` |
| `Rf_!` | `boundedConstructibleLowerShriek` | `boundedConstructibleLowerShriek` |
| `- ⊗ᴸ -` | — | `boundedConstructibleTensor` |
| `RHom(-, -)` | — | `boundedConstructibleHom` |

All functors are restrictions along the fully faithful inclusions of the functors on the ambient
derived categories, exactly as for the `ℓ`-adic rings of `BoundedConstructible`.

## Proofs

That the derived pushforward preserves bounded constructible complexes
(`boundedConstructible_rightDerivedLowerStar_obj`, Deligne's finiteness theorem, SGA 4½
[Th. finitude] 1.1 for the torsion ring `T`) is proved once, by dévissage to constructible sheaves
in degree `0`, from the per-ring single-sheaf statements `finiteTypeDirectImage_single_boundedAbove`
and `finiteTypeDirectImage_single_constructible`. For `O̲`, `isMonoidal_boundedConstructible` and
`isMonoidalClosed_boundedConstructible` (SGA 4½ [Th. finitude] 1.6; Bhatt–Scholze, Section 6.8)
are the per-ring dévissage statements of `BoundedConstructibleTensorPreservation` and
`BoundedConstructibleHomPreservation`.

There is no derived tensor product or derived hom on `Dᵇc(X)⟦T̲⟧`: the bounded constructible
complexes over a torsion ring are not stable under `- ⊗ᴸ -` and `RHom(-, -)`. For `T = ℤ/4` on a
geometric point of characteristic `3`, `Tor_i` and `Ext^i` of `ℤ/2` over `ℤ/4` are `ℤ/2` in every
degree `i ≥ 0`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Dévissage for the pushforward -/

section Devissage

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Over (Spec (.of k))} (f : X ⟶ Y)

omit [Fact (ringChar k).Prime] in
/-- The derived pushforward preserves bounded constructible complexes as soon as the bounded
constructible complexes on `Y` form a triangulated subcategory and the direct image of every
constructible sheaf in degree `0` is bounded above with constructible cohomology sheaves. -/
private lemma boundedConstructible_rightDerivedLowerStar_obj_of
    (htri : (boundedConstructible (condensedRingObj Λ Y.left)).IsTriangulated)
    (hb : ∀ F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left),
      IsConstructibleModuleObject (condensedRingObj Λ X.left) F →
      ∃ b : ℤ, ((R((f.left)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b)
    (hc : ∀ F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left),
      IsConstructibleModuleObject (condensedRingObj Λ X.left) F →
      ∀ q : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Y.left)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((R((f.left)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj F))))
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))}
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    boundedConstructible (condensedRingObj Λ Y.left) ((R((f.left)_*⟦Λ⟧)).obj K) := by
  let P := boundedConstructible (condensedRingObj Λ Y.left)
  have : P.IsTriangulated := htri
  apply prop_of_boundedConstructibleModule
    (P.inverseImage R((f.left)_*⟦Λ⟧)) ?_ hK
  intro F hF
  obtain ⟨b, hb⟩ := hb F hF
  exact ⟨⟨⟨0, ((f.left)_*⟦Λ⟧).isGE_rightDerivedFunctor_obj_singleFunctor F⟩,
    ⟨b, hb⟩⟩, hc F hF⟩

end Devissage

/-! ### The coefficient ring `T̲`, `T` a finite discrete ring in which `ℓ` is nilpotent -/

namespace FiniteDiscreteRingObj

section LowerStar

include ℓ k

variable (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
  [hTd : DiscreteTopology T] [hTf : Finite T] [hT : Fact (IsNilpotent (ℓ : T))]

include hTd hTf hT

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

set_option linter.unusedSectionVars false in
/-- **Deligne's finiteness theorem** for `Rf_*`: for `ℓ` invertible in `k` and a finite discrete
ring `T` in which `ℓ` is nilpotent, the derived pushforward along a morphism of separated
`k`-schemes of finite type carries bounded constructible complexes of `T`-sheaves to bounded
constructible complexes (SGA 4½ [Th. finitude], 1.1). It is false for a general condensed ring: for
the constant discrete ring `𝔽_p` and the affine line over an algebraically closed field of
characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which is
infinite. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj T⟧) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) Y.left)
      ((R((f.left)_*⟦Profinite.continuousMapRingObj T⟧)).obj K.obj) := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  exact boundedConstructible_rightDerivedLowerStar_obj_of _ f
    (isTriangulated_boundedConstructible_finiteDiscreteRingObj Y.left T)
    (FiniteDiscreteRingObj.finiteTypeDirectImage_single_boundedAbove ℓ f T)
    (FiniteDiscreteRingObj.finiteTypeDirectImage_single_constructible ℓ f T) K.property

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦T̲⟧ ⥤ Dᵇc(Y)⟦T̲⟧` on bounded constructible
complexes: the restriction of `R((f)_*⟦T̲⟧)`. -/
noncomputable def boundedConstructibleLowerStar :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj T⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj T⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.continuousMapRingObj T⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ T f K

/-- The restricted derived pushforward is compatible with the inclusions (`T`-coefficient). -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ T f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.continuousMapRingObj T⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes (`T`-coefficient): the
restriction of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ f ⊣
      boundedConstructibleLowerStar ℓ T f :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.continuousMapRingObj T) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ T f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar` (`T`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj T) ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar` (`T`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ T f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes
(`T`-coefficient): the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar ℓ T f ⋙ boundedConstructibleLowerStar ℓ T g ≅
      boundedConstructibleLowerStar ℓ T (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ T (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ T g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ T f))
    (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj T) ℓ f g).symm).symm

end LowerStar

section Shriek

include ℓ k

variable (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
  [hTd : DiscreteTopology T] [hTf : Finite T] [hT : Fact (IsNilpotent (ℓ : T))]

include hTd hTf hT

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦T̲⟧ ⥤ Dᵇc(Y)⟦T̲⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p`, both on bounded constructible complexes, for `i`
and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj T⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj T⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj T) ℓ c.overI ⋙
    boundedConstructibleLowerStar ℓ T c.overG

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦T̲⟧ ⥤ Dᵇc(Y)⟦T̲⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj T⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj T⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ T (compactificationOverField f)

end Shriek

end FiniteDiscreteRingObj

/-! ### The coefficient ring `O̲`, `O` the closed unit ball of a finite extension of `ℚ_ℓ` -/

namespace UnitBallRingObj

section LowerStar

include ℓ k

variable {E : Type} [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [hE : FiniteDimensional ℚ_[ℓ] E]
  (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]

include hE hO

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

set_option linter.unusedSectionVars false in
/-- **Deligne's finiteness theorem** for `Rf_*`: for `ℓ` invertible in `k` and the closed unit
ball `O` of a finite extension `E` of `ℚ_ℓ`, the derived pushforward along a morphism of separated
`k`-schemes of finite type carries bounded constructible complexes of `O`-sheaves to bounded
constructible complexes (SGA 4½ [Th. finitude] for torsion coefficients; Bhatt–Scholze,
Section 6.8, for `O̲`). It is false for a general condensed ring: for the constant discrete ring
`𝔽_p` and the affine line over an algebraically closed field of characteristic `p`, Artin–Schreier
gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which is infinite. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj O⟧) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj O) Y.left)
      ((R((f.left)_*⟦Profinite.continuousMapRingObj O⟧)).obj K.obj) := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  exact boundedConstructible_rightDerivedLowerStar_obj_of _ f
    (isTriangulated_boundedConstructible_unitBallRingObj Y.left ℓ O)
    (UnitBallRingObj.finiteTypeDirectImage_single_boundedAbove ℓ f O)
    (UnitBallRingObj.finiteTypeDirectImage_single_constructible ℓ f O) K.property

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦O̲⟧ ⥤ Dᵇc(Y)⟦O̲⟧` on bounded constructible
complexes: the restriction of `R((f)_*⟦O̲⟧)`. -/
noncomputable def boundedConstructibleLowerStar :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj O⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj O⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.continuousMapRingObj O⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ O f K

/-- The restricted derived pushforward is compatible with the inclusions (`O`-coefficient). -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ O f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.continuousMapRingObj O⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes (`O`-coefficient): the
restriction of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ f ⊣
      boundedConstructibleLowerStar ℓ O f :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj O) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.continuousMapRingObj O) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ O f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar` (`O`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar` (`O`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ O f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes
(`O`-coefficient): the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar ℓ O f ⋙ boundedConstructibleLowerStar ℓ O g ≅
      boundedConstructibleLowerStar ℓ O (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ O (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ O g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ O f))
    (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj O) ℓ f g).symm).symm

end LowerStar

section Shriek

include ℓ k

variable {E : Type} [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [hE : FiniteDimensional ℚ_[ℓ] E]
  (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]

include hE hO

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦O̲⟧ ⥤ Dᵇc(Y)⟦O̲⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p`, both on bounded constructible complexes, for `i`
and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj O⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj O⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj O) ℓ c.overI ⋙
    boundedConstructibleLowerStar ℓ O c.overG

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦O̲⟧ ⥤ Dᵇc(Y)⟦O̲⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj O⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj O⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ O (compactificationOverField f)

end Shriek

section TensorHom

include ℓ k

variable {E : Type} [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [hE : FiniteDimensional ℚ_[ℓ] E]
  (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]

include hE hO

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- The hypotheses of the instance are restated as binders; they repeat section variables.
-- The prime `ℓ` occurs only in the instance `NormedAlgebra ℚ_[ℓ] E`; it is found from the
-- local instance `Fact ℓ.Prime`, so the synthesis order is not the default one.
set_option synthInstance.checkSynthOrder false in
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `O`-sheaves form a monoidal subcategory of
`D(Mod_{O_X})` for the derived tensor product: they contain the unit `O_X` and are
stable under `- ⊗ᴸ -` (SGA 4½ [Th. finitude], 1.6; Bhatt–Scholze, Section 6.8). It is false for a
general condensed ring: for `Λ = ℤ/4` on a geometric point of characteristic `3`,
`Tor_i^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
instance isMonoidal_boundedConstructible
    [Fact ℓ.Prime] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    [Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)] [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left)).IsMonoidal := by
  refine { prop_unit := ?_, prop_tensor := ?_ }
  · exact boundedConstructible_tensor_unit _ X
  · intro K L hK hL
    exact UnitBallRingObj.boundedConstructible_tensor_closure ℓ O K L hK hL

/-- Internal Hom of two constructible `O̲`-sheaves in degree zero is bounded constructible, for the
closed unit ball `O` of a finite normed extension `E` of `ℚ_ℓ` (SGA 4½ [Th. finitude], 1.6;
Bhatt–Scholze, Remark 6.8.15). The coefficient ring `O̲` satisfies `LisseHypotheses`
(`UnitBallRingObj.lisseHypotheses`), so `RHom` preserves bounded constructible complexes by
noetherian induction (`boundedConstructible_ihom_of_over`), the pushforwards along open
immersions preserving them by `boundedConstructible_rightDerivedLowerStar_obj`. -/
theorem boundedConstructible_hom_single
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj O) X.left)
      (((derivedHom (Profinite.continuousMapRingObj O) X.left).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) :=
  boundedConstructible_ihom_of_over (UnitBallRingObj.lisseHypotheses ℓ O) X
    (fun _ _ _ _ _ _ _ _ j _ A hA ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ O j ⟨A, hA⟩)
    (boundedConstructible_singleFunctor_obj _ X.left 0 F hF)
    (boundedConstructible_singleFunctor_obj _ X.left 0 G hG)

-- The hypotheses of the instance are restated as binders; they repeat section variables.
-- The prime `ℓ` occurs only in the instance `NormedAlgebra ℚ_[ℓ] E`; it is found from the
-- local instance `Fact ℓ.Prime`, so the synthesis order is not the default one.
set_option synthInstance.checkSynthOrder false in
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `O`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{O_X})` (SGA 4½ [Th. finitude], 1.6;
Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a geometric
point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
instance isMonoidalClosed_boundedConstructible
    [Fact ℓ.Prime] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    [Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)] [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left)).IsMonoidalClosed :=
  UnitBallRingObj.boundedConstructible_hom_closure X ℓ O
    (boundedConstructible_hom_single ℓ O X)

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦O̲⟧ ⥤ Dᵇc(X)⟦O̲⟧ ⥤ Dᵇc(X)⟦O̲⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the full
subcategory `Dᵇc(X)⟦O̲⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of
`-⊗ᴸ-(X)⟦O̲⟧` in both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj O⟧ ⥤ Dᵇc(X.left)⟦Profinite.continuousMapRingObj O⟧ ⥤
      Dᵇc(X.left)⟦Profinite.continuousMapRingObj O⟧ :=
  curriedTensor _

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦O̲⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj O⟧) :
    (boundedConstructibleTensor ℓ O X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Profinite.continuousMapRingObj O⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

end TensorHom

section MonoidalUpperStar

include ℓ k

variable {E : Type} [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [hE : FiniteDimensional ℚ_[ℓ] E]
  (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]

include hE hO

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦O̲⟧ ⥤ Dᵇc(X)⟦O̲⟧` on bounded constructible complexes
is strong monoidal, with the comparison isomorphisms of `L((f)^*⟦O̲⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj O) ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

end MonoidalUpperStar

end UnitBallRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
