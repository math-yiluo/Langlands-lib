/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Comp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Global
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
public import WeilConjectures.TraceFormula.PurityDevissage
public import WeilConjectures.PoincareDuality.Biduality.Reduction

/-!

# Base change of the exceptional inverse image of a smooth proper morphism across fields

Let `f : Z ⟶ P` be a proper morphism of separated `k₁`-schemes of finite type with a cartesian
square
```
Z' --πZ--> Z
 |f'       |f
 v         v
P' --πP--> P
```
where `f'` is a proper morphism of separated `k₂`-schemes of finite type, and let
`β : πZ^* Rf^! ⟶ Rf'^! πP^*` be the base change map of the exceptional inverse image
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`). This file proves that `β` is an
isomorphism when `f` is smooth of pure relative dimension `d` (for instance the projection
`ℙⁿ_P ⟶ P`) and

* `πP` is weakly étale
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_smooth_of_weaklyEtale`,
  `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_projectiveSpace_of_weaklyEtale`), or
* `P` is the point `Spec k₁` and `πP : Spec k₂ ⟶ Spec k₁` is arbitrary, e.g. a field extension
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_smooth_point`).

More generally `β(N)` is an isomorphism as soon as `πP^*` commutes with `RHom(Rf_* ℚ̄_ℓ, N)`
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth`).

## Proof

*The endomorphism trick.* An endomorphism `t` of `Rf'^! M` with `Rf'_* t` invertible is invertible
(`CategoryTheory.Adjunction.isIso_of_isIso_map_leftAdjoint` for `Rf'_* ⊣ Rf'^!`). Hence `β(N)` is
invertible as soon as `Rf'_* β(N)` is and the two sides are isomorphic in some way
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_iso`).

*Global sections.* Relative Verdier duality says that the duality map
`Rf_* RHom(K, Rf^! N) ⟶ RHom(Rf_* K, N)` of `(Rf_*, ε_N)` is invertible
(`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_counit`, from
`ProEtale.CondensedRing.isIso_verdierExchange`). By the counit property of `β`, the abstract
proper identity `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans` (with
`G = Rf_*`, `G' = Rf'_*`, `Ψ_X = πZ^*`, `Ψ_Y = πP^*`, the proper base change isomorphism as
exchange, the counits as traces and `β(N)`, `𝟙` as dualizing maps) shows that `Rf'_* β(N)` is
invertible as soon as `πP^* RHom(Rf_* ℚ̄_ℓ, N) ⟶ RHom(πP^* Rf_* ℚ̄_ℓ, πP^* N)` is
(`ProEtale.CondensedRing.isIso_lowerStar_map_upperShriekBaseChangeOfMap_app`). This holds for
weakly étale `πP` (`ProEtale.CondensedRing.isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale`,
from `ProEtale.CondensedRing.isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale`) and for any
morphism of points, every complex on a point being dualizable
(`ProEtale.CondensedRing.isIso_nearbyDualityMap_upperStarOfMap_id_point`,
`CategoryTheory.Verdier.isIso_ihomComparison_app_of_exactPairing`).

*An abstract isomorphism.* For `f` smooth of pure relative dimension `d`,
`πZ^* Rf^! N ≅ πZ^* (f^* N ⊗ ℚ̄_ℓ(d)[2d]) ≅ f'^* πP^* N ⊗ ℚ̄_ℓ(d)[2d] ≅ Rf'^! πP^* N`
(`ProEtale.CondensedRing.upperShriekBaseChangeIsoOfSmooth`), by the purity tensor maps
(`ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`), smooth purity
(`ProEtale.CondensedRing.isIso_smoothPurityMap`, from the smooth purity section) and
the pullback of the Tate twists.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Verdier

open Functor.LaxMonoidal

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type*} [Category* C'] [MonoidalCategory C'] [MonoidalClosed C']

/-- **Monoidal functors commute with internal homs out of dualizable objects**: for a monoidal
functor `F` and an object `X` with a left dual `Y`, the comparison `F RHom(X, B) ⟶ RHom(F X, F B)`
is an isomorphism. Both internal homs are identified with tensoring with the duals `Y` and `F Y`
(`CategoryTheory.ExactPairing.map`), and under these identifications the comparison is
`F (Y ⊗ B) ≅ F Y ⊗ F B`. -/
lemma isIso_ihomComparison_app_of_exactPairing (F : C ⥤ C') [F.Monoidal] (Y X : C)
    [ExactPairing Y X] (B : C) : IsIso ((ihomComparison F X).app B) := by
  let := ExactPairing.map F Y X
  let s := (tensorLeftAdjunction Y X).rightAdjointUniq (ihom.adjunction X)
  let s' := (tensorLeftAdjunction (F.obj Y) (F.obj X)).rightAdjointUniq
    (ihom.adjunction (F.obj X))
  have e1 : X ◁ s.hom.app B ≫ (ihom.ev X).app B = (tensorLeftAdjunction Y X).counit.app B :=
    (tensorLeftAdjunction Y X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) B
  have e2 : F.obj X ◁ s'.hom.app (F.obj B) ≫ (ihom.ev (F.obj X)).app (F.obj B) =
      (tensorLeftAdjunction (F.obj Y) (F.obj X)).counit.app (F.obj B) :=
    (tensorLeftAdjunction (F.obj Y) (F.obj X)).rightAdjointUniq_hom_app_counit
      (ihom.adjunction (F.obj X)) (F.obj B)
  have h : F.map (s.hom.app B) ≫ (ihomComparison F X).app B =
      Functor.OplaxMonoidal.δ F Y B ≫ s'.hom.app (F.obj B) := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_eq, ihomComparison_ev, μ_natural_right_assoc,
      ← F.map_comp, e1]
    erw [μ_comp_map_tensorLeftAdjunction_counit_app F Y X B]
    rw [uncurry_natural_left, uncurry_eq, e2]
  have : IsIso (F.map (s.hom.app B) ≫ (ihomComparison F X).app B) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (s.hom.app B)) _

/-- The duality map of a lax monoidal functor `F` with the identity as dualizing map is the
comparison of internal homs of `F`. -/
lemma nearbyDualityMap_id_eq_ihomComparison (F : C ⥤ C') [F.LaxMonoidal] (W X : C) :
    nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ F A B) (𝟙 (F.obj W)) X =
      (ihomComparison F X).app W := by
  rw [nearbyDualityMap_eq_ihomComparison]
  simp

end CategoryTheory.Verdier

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

section Verdier

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z P : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
  [IsSeparated P.hom]

/-- **Relative Verdier duality as a duality map**: for a proper `f : Z ⟶ P`, the duality map
`Rf_* RHom(K, Rf^! N) ⟶ RHom(Rf_* K, N)` of `(Rf_*, μ, ε_N)` (`μ` the lax structure
`boundedConstructibleLowerStarLaxMonoidal`, `ε` the counit of `Rf_* ⊣ Rf^!`) is an isomorphism:
read through `Rf_! ≅ Rf_*` it is the Verdier exchange morphism. -/
theorem isIso_nearbyDualityMap_lowerStar_counit (f : Z ⟶ P) [IsProper f.left]
    (K : Dᵇc(Z.left)⟦𝐐⟧) (N : Dᵇc(P.left)⟦𝐐⟧) :
    IsIso (Verdier.nearbyDualityMap
      (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f;
        Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f))
      ((lowerStarUpperShriekAdjunction ℓ f).counit.app N) K) := by
  have hc : (lowerStarUpperShriekAdjunction ℓ f).counit.app N =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app _ ≫
        (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app N := by
    simp [lowerStarUpperShriekAdjunction]
  have e := Verdier.nearbyDualityMap_comp_pre_eq_exchange
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleExceptionalProjection ℓ f)
    (fun T B ↦ upperStar_map_exceptionalProjection_comp_counit ℓ f T B) K N
  have h₁ : IsIso (Verdier.exchange
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
      (boundedConstructibleUpperShriekAdjunction ℓ f)
      (boundedConstructibleExceptionalProjection ℓ f) K N) :=
    isIso_verdierExchange ℓ f K N
  have h₂ := isIso_pre_app
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K) N
  rw [← e] at h₁
  rw [hc]
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h₂ h₁

end Verdier

section GlobalSections

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ P} {f' : Z' ⟶ P'} [IsProper f.left] [IsProper f'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

/-- `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans` for the pullbacks
`πZ^*`, `πP^*`, the pushforwards `Rf_*`, `Rf'_*` with the counits as traces, for an arbitrary
invertible exchange `χ` and an arbitrary map `γ`; they are kept abstract so that the kernel never
unfolds them. -/
private lemma isIso_lowerStar_map_nearbyDualityMap_aux
    (χ : boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πP ⟶
      boundedConstructibleUpperStarOfMap ℓ πZ ⋙ boundedConstructibleLowerStar ℓ f') [IsIso χ]
    (N : Dᵇc(P.left)⟦𝐐⟧)
    (γ : (boundedConstructibleUpperStarOfMap ℓ πZ).obj
        ((boundedConstructibleUpperShriek ℓ f).obj N) ⟶
      (boundedConstructibleUpperShriek ℓ f').obj ((boundedConstructibleUpperStarOfMap ℓ πP).obj N))
    (hμ : ∀ A B : Dᵇc(Z.left)⟦𝐐⟧,
      (χ.app A ⊗ₘ χ.app B) ≫
        (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f';
          Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f') _ _) ≫
        (boundedConstructibleLowerStar ℓ f').map
          (Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ) A B) =
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP) _ _ ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP).map
          (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f;
            Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f) A B) ≫
        χ.app (A ⊗ B))
    (hθ : (boundedConstructibleUpperStarOfMap ℓ πP).map
          ((lowerStarUpperShriekAdjunction ℓ f).counit.app N) ≫ 𝟙 _ =
      χ.app ((boundedConstructibleUpperShriek ℓ f).obj N) ≫
        (boundedConstructibleLowerStar ℓ f').map γ ≫
        (lowerStarUpperShriekAdjunction ℓ f').counit.app
          ((boundedConstructibleUpperStarOfMap ℓ πP).obj N))
    (M : Dᵇc(Z.left)⟦𝐐⟧)
    (h₅ : IsIso (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP) A B)
      (𝟙 ((boundedConstructibleUpperStarOfMap ℓ πP).obj N))
      ((boundedConstructibleLowerStar ℓ f).obj M))) :
    IsIso ((boundedConstructibleLowerStar ℓ f').map
      (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
        (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ) A B) γ M)) :=
  Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans hμ hθ
    (fun A _ _ y ↦ letI := boundedConstructibleLowerStarLaxMonoidal ℓ f'
      Functor.LaxMonoidal.μ_natural_right _ A y)
    (fun x y ↦ Functor.LaxMonoidal.μ_natural _ x y) M inferInstance inferInstance
    (isIso_nearbyDualityMap_lowerStar_counit ℓ f M N)
    (isIso_nearbyDualityMap_lowerStar_counit ℓ f' _ _) h₅

/-- **Global sections of the base change of `Rf^!`**: for a cartesian square
`πZ ≫ f = f' ≫ πP` with `f`, `f'` proper, and `N` on `P` such that `πP^*` commutes with
`RHom(Rf_* ℚ̄_ℓ, N)` (the duality map `πP^* RHom(Rf_* ℚ̄_ℓ, N) ⟶ RHom(πP^* Rf_* ℚ̄_ℓ, πP^* N)` is
invertible), `Rf'_*` of the base change map `πZ^* Rf^! N ⟶ Rf'^! πP^* N` is invertible. -/
theorem isIso_lowerStar_map_upperShriekBaseChangeOfMap_app
    (sqf : IsPullback πZ f'.left f.left πP) (N : Dᵇc(P.left)⟦𝐐⟧)
    (h : IsIso (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP) A B)
      (𝟙 ((boundedConstructibleUpperStarOfMap ℓ πP).obj N))
      ((boundedConstructibleLowerStar ℓ f).obj (𝟙_ _)))) :
    IsIso ((boundedConstructibleLowerStar ℓ f').map
      ((upperShriekBaseChangeOfMap ℓ sqf).app N)) := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sqf
  have hc := lowerStar_map_upperShriekBaseChangeOfMap_app_comp_counit ℓ sqf N
  have hθ : (boundedConstructibleUpperStarOfMap ℓ πP).map
        ((lowerStarUpperShriekAdjunction ℓ f).counit.app N) ≫ 𝟙 _ =
      (boundedConstructibleBaseChangeOfMap ℓ sqf.toCommSq).app
          ((boundedConstructibleUpperShriek ℓ f).obj N) ≫
        (boundedConstructibleLowerStar ℓ f').map ((upperShriekBaseChangeOfMap ℓ sqf).app N) ≫
        (lowerStarUpperShriekAdjunction ℓ f').counit.app
          ((boundedConstructibleUpperStarOfMap ℓ πP).obj N) := by
    rw [hc, ← NatTrans.comp_app_assoc, IsIso.hom_inv_id, NatTrans.id_app, Category.id_comp,
      Category.comp_id]
  have h' := isIso_lowerStar_map_nearbyDualityMap_aux ℓ
    (boundedConstructibleBaseChangeOfMap ℓ sqf.toCommSq) N
    ((upperShriekBaseChangeOfMap ℓ sqf).app N)
    (boundedConstructibleBaseChangeOfMap_tensor ℓ sqf.toCommSq) hθ (𝟙_ _) h
  exact Verdier.isIso_map_of_isIso_map_nearbyDualityMap_unit (boundedConstructibleLowerStar ℓ f')
    (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ)
    ((upperShriekBaseChangeOfMap ℓ sqf).app N) h'

/-- **The endomorphism trick**: if `Rf'_*` of the base change map
`πZ^* Rf^! N ⟶ Rf'^! πP^* N` is invertible and the two sides are isomorphic in some way, then the
base change map is invertible. -/
theorem isIso_upperShriekBaseChangeOfMap_app_of_iso (sqf : IsPullback πZ f'.left f.left πP)
    (N : Dᵇc(P.left)⟦𝐐⟧)
    (ψ : (boundedConstructibleUpperStarOfMap ℓ πZ).obj
        ((boundedConstructibleUpperShriek ℓ f).obj N) ≅
      (boundedConstructibleUpperShriek ℓ f').obj ((boundedConstructibleUpperStarOfMap ℓ πP).obj N))
    [IsIso ((boundedConstructibleLowerStar ℓ f').map
      ((upperShriekBaseChangeOfMap ℓ sqf).app N))] :
    IsIso ((upperShriekBaseChangeOfMap ℓ sqf).app N) := by
  have : IsIso ((boundedConstructibleLowerStar ℓ f').map
      (ψ.inv ≫ (upperShriekBaseChangeOfMap ℓ sqf).app N)) := by
    rw [Functor.map_comp]
    infer_instance
  have := (lowerStarUpperShriekAdjunction ℓ f').isIso_of_isIso_map_leftAdjoint
    (ψ.inv ≫ (upperShriekBaseChangeOfMap ℓ sqf).app N)
  exact IsIso.of_isIso_comp_left ψ.inv _

end GlobalSections

section PullbackIhom

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]

/-- The comparison of internal homs of the pullback on bounded constructible complexes is that of
the ambient derived pullback. -/
lemma ι_map_ihomComparison_upperStarOfMap_app {P : Over (Spec (.of k₁))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    {P' : Over (Spec (.of k₂))} [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom]
    [IsSeparated P'.hom] (g : P'.left ⟶ P.left) (A B : Dᵇc(P.left)⟦𝐐⟧) :
    (boundedConstructible _).ι.map ((Functor.LaxMonoidal.ihomComparison
        (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') g) A).app B) =
      (Functor.LaxMonoidal.ihomComparison L((g)^*⟦𝐐⟧) A.obj).app B.obj := by
  exact ObjectProperty.ihomComparison_monoidalLift_app_hom L((g)^*⟦𝐐⟧)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K.obj K.property) A B

/-- **Weakly étale pullback commutes with internal homs on bounded constructible complexes**: for
a weakly étale `g : P' ⟶ P`, the duality map `g^* RHom(A, N) ⟶ RHom(g^* A, g^* N)` of `g^*` with
the identity as dualizing map is invertible
(`ProEtale.CondensedRing.isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale`). -/
theorem isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale {P : Over (Spec (.of k₁))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    {P' : Over (Spec (.of k₂))} [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom]
    [IsSeparated P'.hom] (g : P'.left ⟶ P.left) [WeaklyEtale g] (N A : Dᵇc(P.left)⟦𝐐⟧) :
    IsIso (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') g) A B)
      (𝟙 ((boundedConstructibleUpperStarOfMap ℓ g).obj N)) A) := by
  rw [Verdier.nearbyDualityMap_id_eq_ihomComparison]
  have := isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale 𝐐 g A.obj
  have : IsIso ((boundedConstructible _).ι.map ((Functor.LaxMonoidal.ihomComparison
      (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') g) A).app N)) := by
    rw [ι_map_ihomComparison_upperStarOfMap_app]
    infer_instance
  exact isIso_of_reflects_iso _ (boundedConstructible _).ι

/-- **Pullback between points commutes with internal homs**: for `πₛ : Spec k₂ ⟶ Spec k₁`, the
duality map `πₛ^* RHom(A, N) ⟶ RHom(πₛ^* A, πₛ^* N)` of `πₛ^*` with the identity as dualizing map
is invertible: every `A` is dualizable (`ProEtale.CondensedRing.nonempty_hasLeftDual_point`) and
monoidal functors commute with internal homs out of dualizable objects
(`CategoryTheory.Verdier.isIso_ihomComparison_app_of_exactPairing`). -/
theorem isIso_nearbyDualityMap_upperStarOfMap_id_point (πₛ : Spec (.of k₂) ⟶ Spec (.of k₁))
    (N A : Dᵇc((point k₁).left)⟦𝐐⟧) :
    IsIso (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ) A B)
      (𝟙 ((boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).obj N)) A) := by
  obtain ⟨hA⟩ := nonempty_hasLeftDual_point ℓ (k := k₁) A
  rw [Verdier.nearbyDualityMap_id_eq_ihomComparison]
  exact Verdier.isIso_ihomComparison_app_of_exactPairing _ (ᘁA) A N

end PullbackIhom

section Smooth

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

/-- **The two sides of the base change of `Rf^!` are isomorphic for smooth `f`**: for `f`, `f'`
smooth of pure relative dimension `d` and a cartesian square `πZ ≫ f = f' ≫ πP`, there is an
isomorphism `πZ^* Rf^! N ≅ Rf'^! πP^* N`, the composite
```
πZ^* Rf^! N ≅ πZ^* (f^* N ⊗ Rf^! ℚ̄_ℓ) ≅ πZ^* f^* N ⊗ πZ^* ℚ̄_ℓ(d)[2d] ≅ f'^* πP^* N ⊗ ℚ̄_ℓ(d)[2d]
  ≅ f'^* πP^* N ⊗ Rf'^! ℚ̄_ℓ ≅ Rf'^! πP^* N
```
of the purity tensor maps (`ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`),
the monoidality of `πZ^*`, smooth purity (`ProEtale.CondensedRing.isIso_smoothPurityMap`), the
composition of pullbacks and the pullback of the Tate twists
(`ProEtale.CondensedRing.boundedConstructibleUpperStarOfMapTateTwistIso`). -/
noncomputable def upperShriekBaseChangeIsoOfSmooth {f : Z ⟶ P} {f' : Z' ⟶ P'} (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left]
    (sqf : IsPullback πZ f'.left f.left πP) (N : Dᵇc(P.left)⟦𝐐⟧) :
    (boundedConstructibleUpperStarOfMap ℓ πZ).obj ((boundedConstructibleUpperShriek ℓ f).obj N) ≅
      (boundedConstructibleUpperShriek ℓ f').obj
        ((boundedConstructibleUpperStarOfMap ℓ πP).obj N) :=
  have : Smooth f.left := SmoothOfRelativeDimension.smooth d f.left
  have : Smooth f'.left := SmoothOfRelativeDimension.smooth d f'.left
  have := isIso_upperShriekUnitTensorMap_of_smooth ℓ f N
  have := isIso_upperShriekUnitTensorMap_of_smooth ℓ f'
    ((boundedConstructibleUpperStarOfMap ℓ πP).obj N)
  /- `πZ^* f^* N ≅ f'^* πP^* N`. -/
  let e₁ : (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := Z') (πZ ≫ f.left)).obj N ≅
      (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ).obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := Z) f.left).obj N) :=
    ObjectProperty.isoMk _ ((leftDerivedUpperStarCompOfEq 𝐐
      (rfl : πZ ≫ f.left = πZ ≫ f.left)).app N.obj)
  let e₂ : (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := Z') (πZ ≫ f.left)).obj N ≅
      (boundedConstructibleUpperStarOfMap ℓ (X := P') (Y := Z') f'.left).obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP).obj N) :=
    ObjectProperty.isoMk _ ((leftDerivedUpperStarCompOfEq 𝐐 sqf.w.symm).app N.obj)
  let e := e₁.symm ≪≫ e₂
  /- `πZ^* Rf^! ℚ̄_ℓ ≅ Rf'^! ℚ̄_ℓ`. -/
  let t : (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ).obj
      ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _)) ≅
      (boundedConstructibleUpperShriek ℓ f').obj (𝟙_ _) :=
    (boundedConstructibleUpperStarOfMap ℓ πZ).mapIso (asIso (smoothPurityMap ℓ f d)).symm ≪≫
      boundedConstructibleUpperStarOfMapTateTwistIso ℓ πZ d (2 * d) ≪≫
      asIso (smoothPurityMap ℓ f' d)
  (boundedConstructibleUpperStarOfMap ℓ πZ).mapIso (asIso (upperShriekUnitTensorMap ℓ f N)).symm ≪≫
    (Functor.Monoidal.μIso (boundedConstructibleUpperStarOfMap ℓ πZ) _ _).symm ≪≫
    tensorIso e t ≪≫
    asIso (upperShriekUnitTensorMap ℓ f' ((boundedConstructibleUpperStarOfMap ℓ πP).obj N))

end Smooth

section Main

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ P} {f' : Z' ⟶ P'} [IsProper f.left] [IsProper f'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

/-- **Base change of `Rf^!` for a smooth proper morphism, given that `πP^*` commutes with
`RHom(Rf_* ℚ̄_ℓ, N)`**: for `f` proper and smooth of pure relative dimension `d`, a cartesian
square `πZ ≫ f = f' ≫ πP` and `N` on `P` such that the duality map
`πP^* RHom(Rf_* ℚ̄_ℓ, N) ⟶ RHom(πP^* Rf_* ℚ̄_ℓ, πP^* N)` is invertible, the base change map
`πZ^* Rf^! N ⟶ Rf'^! πP^* N` is an isomorphism. -/
theorem isIso_upperShriekBaseChangeOfMap_app_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f.left] (sqf : IsPullback πZ f'.left f.left πP)
    (N : Dᵇc(P.left)⟦𝐐⟧)
    (h : IsIso (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP) A B)
      (𝟙 ((boundedConstructibleUpperStarOfMap ℓ πP).obj N))
      ((boundedConstructibleLowerStar ℓ f).obj (𝟙_ _)))) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sqf).app N) := by
  have : SmoothOfRelativeDimension d f'.left := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback sqf ‹_›
  have := isIso_lowerStar_map_upperShriekBaseChangeOfMap_app ℓ sqf N h
  exact isIso_upperShriekBaseChangeOfMap_app_of_iso ℓ sqf N
    (upperShriekBaseChangeIsoOfSmooth ℓ d sqf N)

/-- **Base change of `Rf^!` for a smooth proper morphism along a weakly étale morphism**: for `f`
proper and smooth of pure relative dimension `d`, and a cartesian square `πZ ≫ f = f' ≫ πP` with
`πP` weakly étale (for instance the inclusion of the generic point of `𝔸¹_k`, changing the base
field from `k` to `k(t)`), the base change map `πZ^* Rf^! N ⟶ Rf'^! πP^* N` is an isomorphism. -/
theorem isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [WeaklyEtale πP] (sqf : IsPullback πZ f'.left f.left πP)
    (N : Dᵇc(P.left)⟦𝐐⟧) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sqf).app N) :=
  isIso_upperShriekBaseChangeOfMap_app_of_smooth ℓ d sqf N
    (isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale ℓ πP N _)

/-- **Base change of `Rf^!` for a smooth proper morphism along a weakly étale morphism**, as an
isomorphism of functors `πZ^* Rf^! ≅ Rf'^! πP^*`. -/
theorem isIso_upperShriekBaseChangeOfMap_of_smooth_of_weaklyEtale (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [WeaklyEtale πP]
    (sqf : IsPullback πZ f'.left f.left πP) : IsIso (upperShriekBaseChangeOfMap ℓ sqf) :=
  have := isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale ℓ d sqf
  NatIso.isIso_of_isIso_app _

end Main

section Point

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Z' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] {f : Z ⟶ point k₁} {f' : Z' ⟶ point k₂} [IsProper f.left]
  [IsProper f'.left] {πₛ : Spec (.of k₂) ⟶ Spec (.of k₁)} {πZ : Z'.left ⟶ Z.left}

/-- **Base change of `Ra^!` for a smooth proper scheme across fields**: for a proper `k₁`-scheme
`Z` smooth of pure dimension `d` with structure morphism `a`, and a cartesian square
`πZ ≫ a = a' ≫ πₛ` over any `πₛ : Spec k₂ ⟶ Spec k₁` (for instance a field extension), the base
change map `πZ^* Ra^! N ⟶ Ra'^! πₛ^* N` is an isomorphism: over a point every complex is
dualizable, so `πₛ^*` commutes with internal homs
(`ProEtale.CondensedRing.isIso_nearbyDualityMap_upperStarOfMap_id_point`). -/
theorem isIso_upperShriekBaseChangeOfMap_app_of_smooth_point (d : ℕ)
    [SmoothOfRelativeDimension d f.left] (sqf : IsPullback πZ f'.left f.left πₛ)
    (N : Dᵇc((point k₁).left)⟦𝐐⟧) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sqf).app N) :=
  isIso_upperShriekBaseChangeOfMap_app_of_smooth ℓ d sqf N
    (isIso_nearbyDualityMap_upperStarOfMap_id_point ℓ πₛ N _)

/-- **Base change of `Ra^!` for a smooth proper scheme across fields**, as an isomorphism of
functors `πZ^* Ra^! ≅ Ra'^! πₛ^*`. -/
theorem isIso_upperShriekBaseChangeOfMap_of_smooth_point (d : ℕ)
    [SmoothOfRelativeDimension d f.left] (sqf : IsPullback πZ f'.left f.left πₛ) :
    IsIso (upperShriekBaseChangeOfMap ℓ sqf) :=
  have := isIso_upperShriekBaseChangeOfMap_app_of_smooth_point ℓ d sqf
  NatIso.isIso_of_isIso_app _

end Point

section Projective

/-- A morphism isomorphic over `S` to the projection `ℙⁿ_S ⟶ S` of a projective space is smooth of
relative dimension `n`. -/
lemma smoothOfRelativeDimension_of_iso_projectiveSpace {X S : Scheme.{u}} (n : ℕ)
    (e : X ≅ ℙ(ULift.{u} (Fin (n + 1)); S)) {f : X ⟶ S}
    (he : e.hom ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = f) : SmoothOfRelativeDimension n f := by
  have : SmoothOfRelativeDimension n (ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S) :=
    ProjectiveSpace.smoothOfRelativeDimension _ _ (by simp)
  rw [← he]
  exact MorphismProperty.RespectsIso.precomp (@SmoothOfRelativeDimension n) e.hom _ this

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ P} {f' : Z' ⟶ P'} [IsProper f.left] [IsProper f'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

/-- **Base change of `Rf^!` for the projection `ℙⁿ_P ⟶ P` along a weakly étale morphism**: for
`f : Z ⟶ P` isomorphic over `P` to the projection of a projective space and a cartesian square
`πZ ≫ f = f' ≫ πP` with `πP` weakly étale, the base change map `πZ^* Rf^! ⟶ Rf'^! πP^*` is an
isomorphism. -/
theorem isIso_upperShriekBaseChangeOfMap_of_projectiveSpace_of_weaklyEtale (n : ℕ)
    (e : Z.left ≅ ℙ(ULift.{u} (Fin (n + 1)); P.left))
    (he : e.hom ≫ ℙ(ULift.{u} (Fin (n + 1)); P.left) ↘ P.left = f.left) [WeaklyEtale πP]
    (sqf : IsPullback πZ f'.left f.left πP) : IsIso (upperShriekBaseChangeOfMap ℓ sqf) :=
  have := smoothOfRelativeDimension_of_iso_projectiveSpace n e he
  isIso_upperShriekBaseChangeOfMap_of_smooth_of_weaklyEtale ℓ n sqf

end Projective

end AlgebraicGeometry.ProEtale.CondensedRing
