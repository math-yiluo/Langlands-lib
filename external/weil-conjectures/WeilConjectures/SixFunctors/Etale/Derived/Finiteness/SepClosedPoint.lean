/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!
# Perfect complexes on a separably closed point

Let `k` be a separably closed field, `s = Spec k`, and `Λ` a commutative ring. The constant
sheaf functor `F : ModuleCat Λ ⥤ Sheaf s_ét (ModuleCat Λ)` is a monoidal equivalence, with
quasi-inverse the global sections, so the derived global sections `RΓ(s, -) ≅ D(F⁻¹)` are an
equivalence `D(s_ét, Λ) ≌ D(Λ)` which commutes with homology and with the derived tensor
products. This file transports the three ingredients of perfectness along it: for `L` in
`D(s_ét, Λ)`,

* `Hⁿ(RΓ(s, L)) ≅ F⁻¹(Hⁿ L)` is a finite `Λ`-module if `Hⁿ L` is constructible;
* `RΓ(s, L)` is bounded if `L` is;
* `RΓ(s, L)` has Tor amplitude in `[a, b]` if `L` has.

Hence `RΓ(s, L)` is a perfect complex of `Λ`-modules for `L ∈ Dctf(s, Λ)` and `Λ` Noetherian.

## Main statements

- `DerivedCategory.torAmplitudeIn_of_mapDerivedCategory`: a monoidal equivalence of abelian
  categories reflects Tor amplitude.
- `AlgebraicGeometry.Etale.moduleFinite_homology_rightDerivedGlobalSections_of_isSepClosed`
- `AlgebraicGeometry.Etale.homologyConcentratedIn_rightDerivedGlobalSections_of_isSepClosed`
- `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed`
- `AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections_of_isSepClosed`
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {C₁ C₂ : Type*} [Category.{v} C₁] [Abelian C₁] [IsGrothendieckAbelian.{v} C₁]
  [HasDerivedCategory.{v} C₁] [MonoidalCategory C₁] [MonoidalClosed C₁] [MonoidalPreadditive C₁]
  [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
  [Category.{v} C₂] [Abelian C₂] [IsGrothendieckAbelian.{v} C₂]
  [HasDerivedCategory.{v} C₂] [MonoidalCategory C₂] [MonoidalClosed C₂] [MonoidalPreadditive C₂]
  [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]
  (F : C₁ ⥤ C₂) [F.Monoidal] [F.IsEquivalence] [F.Additive]

omit [IsGrothendieckAbelian.{v} C₁] [MonoidalCategory C₁] [MonoidalClosed C₁]
  [MonoidalPreadditive C₁] [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
  [IsGrothendieckAbelian.{v} C₂] [MonoidalCategory C₂] [MonoidalClosed C₂]
  [MonoidalPreadditive C₂] [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]
  [F.Monoidal] in
/-- For an additive equivalence `F`, an object `X` of `D(C₁)` whose image `D(F) X` has
homology concentrated in `[a, b]` has itself homology concentrated in `[a, b]`: `D(F)` commutes
with homology and `F` reflects zero objects. -/
lemma homologyConcentratedIn_of_mapDerivedCategory {a b : ℤ} (X : DerivedCategory C₁)
    (hX : homologyConcentratedIn a b (F.mapDerivedCategory.obj X)) :
    homologyConcentratedIn a b X := by
  have key (q : ℤ) (hq : IsZero ((homologyFunctor _ q).obj (F.mapDerivedCategory.obj X))) :
      IsZero ((homologyFunctor _ q).obj X) := by
    have h : IsZero (F.obj ((homologyFunctor _ q).obj X)) :=
      hq.of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app X)
    exact (F.inv.map_isZero h).of_iso (F.asEquivalence.unitIso.app _)
  obtain ⟨h₁, h₂⟩ := hX
  exact ⟨(isGE_iff _ a).2 fun q hq ↦ key q ((isGE_iff _ a).1 h₁ q hq),
    (isLE_iff _ b).2 fun q hq ↦ key q ((isLE_iff _ b).1 h₂ q hq)⟩

/-- A monoidal additive equivalence `F` of abelian categories reflects Tor amplitude: if
`D(F) X` has Tor amplitude in `[a, b]`, so has `X`, since
`D(F)(X ⊗ᴸ M) ≅ D(F) X ⊗ᴸ F(M)` for every object `M` of `C₁`. -/
lemma torAmplitudeIn_of_mapDerivedCategory {a b : ℤ} (X : DerivedCategory C₁)
    (hX : torAmplitudeIn C₂ a b (F.mapDerivedCategory.obj X)) :
    torAmplitudeIn C₁ a b X := fun M ↦
  homologyConcentratedIn_of_mapDerivedCategory F _
    ((homologyConcentratedIn a b).prop_of_iso
      (((tensorLeftCompMapDerivedCategoryIso F X).app _) ≪≫
        whiskerLeftIso _ ((F.mapDerivedCategorySingleFunctor 0).app M)).symm (hX (F.obj M)))

section

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{v} C] [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- A zero object has Tor amplitude in every interval. -/
lemma torAmplitudeIn_of_isZero (a b : ℤ) {K : DerivedCategory C} (hK : IsZero K) :
    torAmplitudeIn C a b K := fun F ↦ by
  have h : IsZero (K ⊗ (singleFunctor C 0).obj F) :=
    (tensorRight ((singleFunctor C 0).obj F)).map_isZero hK
  have h' (i : ℤ) := (homologyFunctor C i).map_isZero h
  exact ⟨(isGE_iff _ a).2 fun i _ ↦ h' i, (isLE_iff _ b).2 fun i _ ↦ h' i⟩

end

end DerivedCategory

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

section

variable (Λ k) in
/-- The constant sheaf functor `ModuleCat Λ ⥤ Sheaf (Spec k)_ét (ModuleCat Λ)`, an equivalence
for `k` separably closed. -/
noncomputable abbrev pointConstantSheaf :
    ModuleCat.{u + 1} Λ ⥤ Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)

instance : (pointConstantSheaf Λ k).Additive :=
  inferInstanceAs (constantSheaf _ _).Additive

instance : (pointConstantSheaf Λ k).asEquivalence.functor.Additive :=
  inferInstanceAs (pointConstantSheaf Λ k).Additive

instance : (pointConstantSheaf Λ k).inv.Additive :=
  inferInstanceAs (pointConstantSheaf Λ k).asEquivalence.inverse.Additive

instance : PreservesFiniteLimits (pointConstantSheaf Λ k).inv :=
  inferInstanceAs (PreservesFiniteLimits (pointConstantSheaf Λ k).asEquivalence.inverse)

instance : PreservesFiniteColimits (pointConstantSheaf Λ k).inv :=
  inferInstanceAs (PreservesFiniteColimits (pointConstantSheaf Λ k).asEquivalence.inverse)

/-- A finite étale sheaf `G` on a separably closed point has a finite value
`F⁻¹ G = Γ(s, G)`: it is the stalk of `G` at the identity geometric point. -/
lemma moduleFinite_pointConstantSheaf_inv_obj
    (G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : Scheme.IsFiniteSheaf (A := ModuleCat.{u + 1} Λ) G) :
    Module.Finite Λ ((pointConstantSheaf Λ k).inv.obj G) := by
  have h := hG.isFinitelyGenerated_sheafFiber k (𝟙 _)
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := Scheme.pointSmallEtale (𝟙 (Spec (.of k)))
  let e : Φ.sheafFiber.obj G ≅ (pointConstantSheaf Λ k).inv.obj G :=
    Φ.sheafFiber.mapIso ((pointConstantSheaf Λ k).asEquivalence.counitIso.app G).symm ≪≫
      Φ.sheafFiberConstantSheafIso _
  exact (ModuleCat.isFinitelyGenerated_iff _).1
    ((ConcreteCategory.isFinitelyGenerated_iff_of_iso e).1 h)

end

variable (L : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
  (ModuleCat.{u + 1} Λ)))

/-- On a separably closed point, the homology of the derived global sections is the value of
the quasi-inverse of the constant sheaf functor on the homology sheaves:
`Hⁿ(RΓ(s, L)) ≅ F⁻¹(Hⁿ L)`. -/
noncomputable def homologyRightDerivedGlobalSectionsIsoPointConstantSheafInv (n : ℤ) :
    (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj L) ≅
      (pointConstantSheaf Λ k).inv.obj ((_root_.DerivedCategory.homologyFunctor _ n).obj L) :=
  (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).mapIso
      ((rightDerivedGlobalSectionsIsoMapDerivedCategoryInv _ _).app L) ≪≫
    (((pointConstantSheaf Λ k).inv.mapDerivedCategoryHomologyFunctorIso n).app L).symm

/-- On a separably closed point, the homology modules of `RΓ(s, L)` are finite as soon as the
homology sheaves of `L` are finite (for instance constructible). -/
theorem moduleFinite_homology_rightDerivedGlobalSections_of_isSepClosed (n : ℤ)
    (hL : Scheme.IsFiniteSheaf (A := ModuleCat.{u + 1} Λ)
      ((_root_.DerivedCategory.homologyFunctor _ n).obj L)) :
    Module.Finite Λ ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj L)) :=
  have := moduleFinite_pointConstantSheaf_inv_obj _ hL
  Module.Finite.equiv
    (homologyRightDerivedGlobalSectionsIsoPointConstantSheafInv L n).toLinearEquiv.symm

/-- On a separably closed point, `RΓ(s, L)` has homology concentrated in `[a, b]` if `L` has. -/
theorem homologyConcentratedIn_rightDerivedGlobalSections_of_isSepClosed {a b : ℤ}
    (hL : _root_.DerivedCategory.homologyConcentratedIn a b L) :
    _root_.DerivedCategory.homologyConcentratedIn a b
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj L) := by
  have key (q : ℤ) (hq : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj L)) :
      IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj L)) :=
    ((pointConstantSheaf Λ k).inv.map_isZero hq).of_iso
      (homologyRightDerivedGlobalSectionsIsoPointConstantSheafInv L q)
  obtain ⟨h₁, h₂⟩ := hL
  exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 fun q hq ↦
      key q ((_root_.DerivedCategory.isGE_iff L a).1 h₁ q hq),
    (_root_.DerivedCategory.isLE_iff _ b).2 fun q hq ↦
      key q ((_root_.DerivedCategory.isLE_iff L b).1 h₂ q hq)⟩

/-- On a separably closed point `s = Spec k`, the derived global sections `RΓ(s, L)` of an
object `L ∈ Dctf(s, Λ)` are a perfect complex of `Λ`-modules, for `Λ` Noetherian. -/
theorem isPerfect_rightDerivedGlobalSections_of_isSepClosed [IsNoetherianRing Λ]
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k)) L) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj L).IsPerfect := by
  obtain ⟨⟨hb, hc⟩, a, b, hta⟩ := hL
  obtain ⟨c, d, hcd⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded L).2 hb
  refine _root_.DerivedCategory.isPerfect_of_finiteTorAmplitude
    ((_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
      ⟨c, d, homologyConcentratedIn_rightDerivedGlobalSections_of_isSepClosed L hcd⟩)
    (fun n ↦ moduleFinite_homology_rightDerivedGlobalSections_of_isSepClosed L n
      (Scheme.IsConstructibleSheaf.isFiniteSheaf (hc n)))
    ⟨a, b, torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed hta⟩

end AlgebraicGeometry.Etale
