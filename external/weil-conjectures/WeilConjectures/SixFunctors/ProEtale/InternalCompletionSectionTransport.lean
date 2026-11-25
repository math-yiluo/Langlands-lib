/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData

/-! # Exact conservative transport of integral complexes to the constant small site

Source: integral-models proof (1), Stacks Tags 00YV and 099I.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport

open IntegralModelsStacks

/-- Section-action transport and small-site restriction form an equivalence.
Source: Stacks Tag 00YV. Proof: compose the section-module equivalence with
pushforward along the inverse of AsSmall.equiv.
(auxiliary; not a blueprint node). -/
theorem smallModules_equivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).IsEquivalence := by
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R)
  let B := ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj A
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsContinuous
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
        X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (J := Scheme.ProEt.topology X)
    (K := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  exact inferInstanceAs
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor ⋙ e.inverse).IsEquivalence

instance smallModules_isEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).IsEquivalence := smallModules_equivalence X R

instance smallModules_additive (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).Additive := ⟨by intros; ext U x; rfl⟩

private theorem derived_reflects
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.ReflectsIsomorphisms] :
    F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects f _ := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso (F.map ((DerivedCategory.homologyFunctor A n).map f)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ F

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The constant coefficient on the large pro-etale site.
Source: integral-models proof (1)
(auxiliary; not a blueprint node). -/
abbrev constantRing := condensedRingObj
  (discreteObj (Padic.coefficientExtensionIntegers l E)) X

/-- The constant section ring on the equivalent small site.
Source: integral-models proof (1)
(auxiliary; not a blueprint node). -/
abbrev ring := smallRing X (constantRing l E X)

/-- First residue map on the small site.
Source: integral-models proof (1)
(auxiliary; not a blueprint node). -/
abbrev residue := smallMap X (residueMap l E X)

/-- Derived restriction to constant coefficients, followed by the exact section equivalence.
Every functor is the prescribed restriction, rather than a chosen equivalence.
Source: integral-models proof (1)
(auxiliary; not a blueprint node). -/
def functor : DerivedCategory (AdicCompletion.Modules l E X) ⥤
    ConstantCompletion.D (ring l E X) :=
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ring l E X))
  (Mod.comap (coefficientMap
    (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory ⋙
    restriction l E X ⋙ (smallModules X (constantRing l E X)).mapDerivedCategory

/-- This transport detects isomorphisms. Proof: ordinary restriction of scalars is
conservative since its composite with the underlying-object functor is unchanged;
exactness and the homology comparison give conservativity after deriving. The final
section functor is an equivalence. Source: Stacks Tags 00YV and 099I
(auxiliary; not a blueprint node). -/
instance functor_reflects : (functor l E X).ReflectsIsomorphisms := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ring l E X))
  have hr {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
      [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
      (f : R ⟶ S) [IsMonHom f] :
      Functor.ReflectsIsomorphisms
        ((Mod.comap f : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S ⥤
          Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R).mapDerivedCategory) := by
    have : (Mod.comap f : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S ⥤
        Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R).ReflectsIsomorphisms :=
      reflectsIsomorphisms_of_comp (Mod.comap f) (Mod.forget R)
    exact derived_reflects _
  have := hr (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  have := hr (scalarMap l E X)
  have := derived_reflects (smallModules X (constantRing l E X))
  unfold functor restriction
  infer_instance

/-- Comparison with the representative-based smallDerivedObject in the target.
Proof: the exact functor localization comparison evaluated at objPreimage, followed
by its image of objObjPreimageIso. Source: Stacks Tag 05RU
(auxiliary; not a blueprint node). -/
def objectIso (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (functor l E X).obj K ≅ smallDerivedObject X _
      ((restriction l E X).obj
        ((Mod.comap (coefficientMap
          (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory.obj K)) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ring l E X))
  let L := (restriction l E X).obj
    ((Mod.comap (coefficientMap
      (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory.obj K)
  let F := smallModules X (constantRing l E X)
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso L).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage L)

/-- Completeness is invariant under isomorphism.
Source: Stacks Tag 0999. Proof: derived restriction and derived internal Hom
carry an isomorphism to an isomorphism, preserving zero objects on every slice.
(auxiliary; not a blueprint node). -/
theorem complete_iso {K L : ConstantCompletion.D (ring l E X)} (e : K ≅ L) :
    ConstantCompletion.IsComplete (residue l E X) K ↔
      ConstantCompletion.IsComplete (residue l E X) L := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ring l E X))
  let (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :=
    HasDerivedCategory.standard (ConstantCompletion.Mod ((ring l E X).over U))
  have h {K L : ConstantCompletion.D (ring l E X)} (e : K ≅ L)
      (hK : ConstantCompletion.IsComplete (residue l E X) K) :
      ConstantCompletion.IsComplete (residue l E X) L := by
    intro U f hf
    let H := (Functor.curry.obj (derivedInternalHom _ ((ring l E X).over U))).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization ((ring l E X).over U)
          (ringedSliceSection (ring l E X) U f))))
    exact (((ringedDerivedRestriction (ring l E X) U ⋙ H).mapIso e).isZero_iff).mp
      (hK U f hf)
  exact ⟨h e, h e.symm⟩

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
